#include "preproc/preprocessing_passes_core.h"

#include <unordered_map>
#include <string>
#include <stack>
#include "expr/node_manager_attributes.h"
#include "expr/node_self_iterator.h"
#include "smt_util/boolean_simplification.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/macros.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/sep/theory_sep_rewriter.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/bv_bitblast_mode.h"
#include "options/bv_options.h"
#include "options/uf_options.h"
#include "options/arith_options.h"
#include "util/ntuple.h"

using namespace std;

namespace CVC4 {

using namespace theory;

namespace preproc {

ExpandingDefinitionsPass::ExpandingDefinitionsPass() : PreprocessingPass("expandingDefinitions", true){
}

void ExpandingDefinitionsPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
  d_smt = smt; 
}

Node ExpandingDefinitionsPass::expandDefinitions(TNode n, unordered_map<Node, Node, NodeHashFunction>& cache, bool expandOnly)
 throw(TypeCheckingException, LogicException, UnsafeInterruptException) {
  stack< triple<Node, Node, bool> > worklist;
  stack<Node> result;
  worklist.push(make_triple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the output / rewritten node
  // and finally a flag tracking whether the children have been explored (i.e. if this is a downward
  // or upward pass).

  do {
    spendResource(options::preprocessStep());
    n = worklist.top().first;                      // n is the input / original
    Node node = worklist.top().second;             // node is the output / result
    bool childrenPushed = worklist.top().third;
    worklist.pop();

    // Working downwards
    if(!childrenPushed) {
      Kind k = n.getKind();

      // Apart from apply, we can short circuit leaves
      if(k != kind::APPLY && n.getNumChildren() == 0) {
        SmtEngine::DefinedFunctionMap::const_iterator i = d_smt->d_definedFunctions->find(n);
        if(i != d_smt->d_definedFunctions->end()) {
          // replacement must be closed
          if((*i).second.getFormals().size() > 0) {
            result.push(d_smt->d_nodeManager->mkNode(kind::LAMBDA, d_smt->d_nodeManager->mkNode(kind::BOUND_VAR_LIST, (*i).second.getFormals()), (*i).second.getFormula()));
            continue;
          }
          // don't bother putting in the cache
          result.push((*i).second.getFormula());
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit = cache.find(n);
     if(cacheHit != cache.end()) {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it
      bool doExpand = k == kind::APPLY;
      if( !doExpand ){
        if( options::macrosQuant() ){
          //expand if we have inferred an operator corresponds to a defined function
          doExpand = k==kind::APPLY_UF && d_smt->isDefinedFunction( n.getOperator().toExpr() );
        }
      }
      if (doExpand) {
        vector<Node> formals;
        TNode fm;
        if( n.getOperator().getKind() == kind::LAMBDA ){
          TNode op = n.getOperator();
          // lambda
          for( unsigned i=0; i<op[0].getNumChildren(); i++ ){
            formals.push_back( op[0][i] );
          }
          fm = op[1];
        }else{
          // application of a user-defined symbol
          TNode func = n.getOperator();
          SmtEngine::DefinedFunctionMap::const_iterator i = d_smt->d_definedFunctions->find(func);
          if(i == d_smt->d_definedFunctions->end()) {
            throw TypeCheckingException(n.toExpr(), string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (*i).second;
          formals = def.getFormals();

          if(Debug.isOn("expand")) {
            Debug("expand") << "found: " << n << endl;
            Debug("expand") << " func: " << func << endl;
            string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << endl;
          }
          if(Debug.isOn("expand")) {
            Debug("expand") << " defn: " << def.getFunction() << endl
                            << "       [";
            if(formals.size() > 0) {
              copy( formals.begin(), formals.end() - 1,
                    ostream_iterator<Node>(Debug("expand"), ", ") );
              Debug("expand") << formals.back();
            }
            Debug("expand") << "]" << endl
                            << "       " << def.getFunction().getType() << endl
                            << "       " << def.getFormula() << endl;
          }

          fm = def.getFormula();
        }

        Node instance = fm.substitute(formals.begin(), formals.end(),
                                      n.begin(), n.end());
        Debug("expand") << "made : " << instance << endl;

        Node expanded = expandDefinitions(instance, cache, expandOnly);
        cache[n] = (n == expanded ? Node::null() : expanded);
        result.push(expanded);
        continue;

      } else if(! expandOnly) {
        // do not do any theory stuff if expandOnly is true

        theory::Theory* t = d_smt->d_theoryEngine->theoryOf(node);

        Assert(t != NULL);
        LogicRequest req(*d_smt);
        node = t->expandDefinition(req, n);
      }

      // there should be children here, otherwise we short-circuited a result-push/continue, above
      if (node.getNumChildren() == 0) {
        Debug("expand") << "Unexpectedly no children..." << node << endl;
      }
      // This invariant holds at the moment but it is concievable that a new theory
      // might introduce a kind which can have children before definition expansion but doesn't
      // afterwards.  If this happens, remove this assertion.
      Assert(node.getNumChildren() > 0);

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(make_triple(Node(n), node, true));            // Original and rewritten result

      for(size_t i = 0; i < node.getNumChildren(); ++i) {
        worklist.push(make_triple(node[i], node[i], false));      // Rewrite the children of the result only
      }

    } else {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << endl;
      //cout << "cons : " << node << endl;
      NodeBuilder<> nb(node.getKind());
      if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
        Debug("expand") << "op   : " << node.getOperator() << endl;
        //cout << "op   : " << node.getOperator() << endl;
        nb << node.getOperator();
      }
      for(size_t i = 0; i < node.getNumChildren(); ++i) {
        Assert(!result.empty());
        Node expanded = result.top();
        result.pop();
        //cout << "exchld : " << expanded << endl;
        Debug("expand") << "exchld : " << expanded << endl;
        nb << expanded;
      }
      node = nb;
      cache[n] = n == node ? Node::null() : node;           // Only cache once all subterms are expanded
      result.push(node);
    } } while(!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

PreprocessingPassResult ExpandingDefinitionsPass::apply(AssertionPipeline* assertionsToPreprocess){
  Chat() << "expanding definitions..." << std::endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_timer);
    unordered_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      assertionsToPreprocess->replace(i, expandDefinitions((*assertionsToPreprocess)[i], cache));
    }
  return PreprocessingPassResult(true);
}

// TODO: Change PreprocessingPass to not expect a ResourceManager* in the
// constructor anymore
NlExtPurifyPass::NlExtPurifyPass() : PreprocessingPass("nlExtPurify", true) {
}

void NlExtPurifyPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 


PreprocessingPassResult NlExtPurifyPass::apply(AssertionPipeline* assertionsToPreprocess) {
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::unordered_map<Node, Node, NodeHashFunction> bcache;
  std::vector<Node> var_eq;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(i, purifyNlTerms((*assertionsToPreprocess)[i], cache, bcache, var_eq));
  }
  if (!var_eq.empty()) {
    unsigned lastIndex = assertionsToPreprocess->size() - 1;
    var_eq.insert(var_eq.begin(), (*assertionsToPreprocess)[lastIndex]);
    assertionsToPreprocess->replace(lastIndex, NodeManager::currentNM()->mkNode(kind::AND, var_eq) );
  }
  return PreprocessingPassResult(true);
}

Node NlExtPurifyPass::purifyNlTerms(TNode n, NodeMap& cache,
   NodeMap& bcache, std::vector<Node>& var_eq, bool beneathMult) {
  if (beneathMult) {
    NodeMap::iterator find = bcache.find(n);
    if (find != bcache.end()) {
      return (*find).second;
    }
  } else {
    NodeMap::iterator find = cache.find(n);
    if (find != cache.end()) {
      return (*find).second;
    }
  }
  Node ret = n;
  if (n.getNumChildren() > 0) {
    if (beneathMult && n.getKind() != kind::MULT) {
      // new variable
      ret = NodeManager::currentNM()->mkSkolem(
          "__purifyNl_var", n.getType(),
          "Variable introduced in purifyNl pass");
      Node np = purifyNlTerms(n, cache, bcache, var_eq, false);
      var_eq.push_back(np.eqNode(ret));
    } else {
      bool beneathMultNew = beneathMult || n.getKind() == kind::MULT;
      bool childChanged = false;
      std::vector<Node> children;
      for (unsigned i = 0; i < n.getNumChildren(); i++) {
        Node nc = purifyNlTerms(n[i], cache, bcache, var_eq, beneathMultNew);
        childChanged = childChanged || nc != n[i];
        children.push_back(nc);
      }
      if (childChanged) {
        ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
      }
    }
  }
  if (beneathMult) {
    bcache[n] = ret;
  } else {
    cache[n] = ret;
  }
  return ret;
}

CEGuidedInstPass::CEGuidedInstPass() : PreprocessingPass("ceGuidedInst", true) {
}

 void CEGuidedInstPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_theoryEngine = theoryEngine;
} 

PreprocessingPassResult CEGuidedInstPass::apply(AssertionPipeline* assertionsToPreprocess){
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      d_theoryEngine->getQuantifiersEngine()->getCegInstantiation()->preregisterAssertion( (*assertionsToPreprocess)[i] );
    }
    return PreprocessingPassResult(true);
}

SolveRealAsIntPass::SolveRealAsIntPass() : PreprocessingPass("solveRealAsInt", true){
}

void SolveRealAsIntPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 

PreprocessingPassResult SolveRealAsIntPass::apply(AssertionPipeline* assertionsToPreprocess) {
 Chat() << "converting reals to ints..." << std::endl;
 std::unordered_map<Node, Node, NodeHashFunction> cache;
 std::vector<Node> var_eq;
 for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
 assertionsToPreprocess->replace(i, realToInt((*assertionsToPreprocess)[i], cache, var_eq) );
 }
   /* these comments were here before
    if( !var_eq.empty() ){
      unsigned lastIndex = d_assertions.size()-1;
      var_eq.insert( var_eq.begin(), d_assertions[lastIndex] );
      d_assertions.replace(last_index, NodeManager::currentNM()->mkNode( kind::AND, var_eq ) );
    }
    */
 return PreprocessingPassResult(true);
}

Node SolveRealAsIntPass::realToInt(TNode n, NodeMap& cache, std::vector< Node >& var_eq) {
  Trace("real-as-int-debug") << "Convert : " << n << std::endl;
  NodeMap::iterator find = cache.find(n);
  if (find != cache.end()) {
    return (*find).second;
  }else{
    Node ret = n;
    if( n.getNumChildren()>0 ){
      if( n.getKind()==kind::EQUAL || n.getKind()==kind::GEQ || n.getKind()==kind::LT || n.getKind()==kind::GT || n.getKind()==kind::LEQ ){
        ret = theory::Rewriter::rewrite( n );
        Trace("real-as-int-debug") << "Now looking at : " << ret << std::endl;
        if( !ret.isConst() ){
          Node ret_lit = ret.getKind()==kind::NOT ? ret[0] : ret;
          bool ret_pol = ret.getKind()!=kind::NOT;
          std::map< Node, Node > msum;
          if( theory::QuantArith::getMonomialSumLit( ret_lit, msum ) ){
            //get common coefficient
            std::vector< Node > coeffs;
            for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
              Node v = itm->first;
              Node c = itm->second;
              if( !c.isNull() ){
                Assert( c.isConst() );
                coeffs.push_back( NodeManager::currentNM()->mkConst( Rational( c.getConst<Rational>().getDenominator() ) ) );
              }
            }
            Node cc = coeffs.empty() ? Node::null() : ( coeffs.size()==1 ? coeffs[0] : theory::Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, coeffs ) ) );
            std::vector< Node > sum;
            for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
              Node v = itm->first;
              Node c = itm->second;
              Node s;
              if( c.isNull() ){
                c = cc.isNull() ? NodeManager::currentNM()->mkConst( Rational( 1 ) ) : cc;
              }else{
                if( !cc.isNull() ){
                  c = theory::Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, c, cc ) );
                }
              }
              Assert( c.getType().isInteger() );
              if( v.isNull() ){
                sum.push_back( c );
              }else{
                Node vv = realToInt( v, cache, var_eq );
                if( vv.getType().isInteger() ){
                  sum.push_back( NodeManager::currentNM()->mkNode( kind::MULT, c, vv ) );
                }else{
                  throw TypeCheckingException(v.toExpr(), std::string("Cannot translate to Int: ") + v.toString());
                }
              }
            }
            Node sumt = sum.empty() ? NodeManager::currentNM()->mkConst( Rational( 0 ) ) : ( sum.size()==1 ? sum[0] : NodeManager::currentNM()->mkNode( kind::PLUS, sum ) );
            ret = NodeManager::currentNM()->mkNode( ret_lit.getKind(), sumt, NodeManager::currentNM()->mkConst( Rational( 0 ) ) );
            if( !ret_pol ){
              ret = ret.negate();
            }
            Trace("real-as-int") << "Convert : " << std::endl;
            Trace("real-as-int") << "   " << n << std::endl;
            Trace("real-as-int") << "   " << ret << std::endl;
          }else{
            throw TypeCheckingException(n.toExpr(), std::string("Cannot translate to Int: ") + n.toString());
          }
        }
      }else{
        bool childChanged = false;
        std::vector< Node > children;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = realToInt( n[i], cache, var_eq );
          childChanged = childChanged || nc!=n[i];
          children.push_back( nc );
        }
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
    }else{
      if( n.isVar() ){
        if( !n.getType().isInteger() ){
          ret = NodeManager::currentNM()->mkSkolem("__realToInt_var", NodeManager::currentNM()->integerType(), "Variable introduced in realToInt pass");
          var_eq.push_back( n.eqNode( ret ) );
        }
      }
    }
    cache[n] = ret;
    return ret;
  }
}

SolveIntAsBVPass::SolveIntAsBVPass() : PreprocessingPass("solveIntAsbv", true){
}

void SolveIntAsBVPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 

PreprocessingPassResult SolveIntAsBVPass::apply(AssertionPipeline* assertionsToPreprocess)
{
  Chat() << "converting ints to bit-vectors..." << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
  assertionsToPreprocess->replace(i, intToBV((*assertionsToPreprocess)[i], cache) );
  }
 return PreprocessingPassResult(true);
}

struct intToBV_stack_element {
  TNode node;
  bool children_added;
  intToBV_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct intToBV_stack_element */

Node SolveIntAsBVPass::intToBVMakeBinary(TNode n, NodeMap& cache) {
  // Do a topological sort of the subexpressions and substitute them
  std::vector<intToBV_stack_element> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    NodeMap::iterator find = cache.find(current);
    if (find != cache.end()) {
      toVisit.pop_back();
      continue;
    }
    if (stackHead.children_added) {
      // Children have been processed, so rebuild this node
      Node result;
      NodeManager* nm = NodeManager::currentNM();
      if (current.getNumChildren() > 2 && (current.getKind() == kind::PLUS || current.getKind() == kind::MULT)) {
        Assert(cache.find(current[0]) != cache.end());
        result = cache[current[0]];
        for (unsigned i = 1; i < current.getNumChildren(); ++ i) {
          Assert(cache.find(current[i]) != cache.end());
          Node child = current[i];
          Node childRes = cache[current[i]];
          result = nm->mkNode(current.getKind(), result, childRes);
        }
      }
      else {
        NodeBuilder<> builder(current.getKind());
        for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
          Assert(cache.find(current[i]) != cache.end());
          builder << cache[current[i]];
        }
        result = builder;
      }
      cache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        cache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  return cache[n];
}

Node SolveIntAsBVPass::intToBV(TNode n, NodeMap& cache) {
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  AlwaysAssert(!options::incrementalSolving());

  std::vector<intToBV_stack_element> toVisit;
  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(n, binaryCache);
  toVisit.push_back(TNode(n_binary));

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    // If node is already in the cache we're done, pop from the stack
    NodeMap::iterator find = cache.find(current);
    if (find != cache.end()) {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    NodeManager* nm = NodeManager::currentNM();
    if (stackHead.children_added) {
      // Children have been processed, so rebuild this node
      std::vector<Node> children;
      unsigned max = 0;
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(cache.find(current[i]) != cache.end());
        TNode childRes = cache[current[i]];
        TypeNode type = childRes.getType();
        if (type.isBitVector()) {
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize > max) {
            max = bvsize;
          }
        }
        children.push_back(childRes);
      }

      kind::Kind_t newKind = current.getKind();
      if (max > 0) {
        switch (newKind) {
          case kind::PLUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_PLUS;
            max = max + 1;
            break;
          case kind::MULT:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_MULT;
            max = max * 2;
            break;
          case kind::MINUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_SUB;
            max = max + 1;
            break;
          case kind::UMINUS:
            Assert(children.size() == 1);
            newKind = kind::BITVECTOR_NEG;
            max = max + 1;
            break;
          case kind::LT:
            newKind = kind::BITVECTOR_SLT;
            break;
          case kind::LEQ:
            newKind = kind::BITVECTOR_SLE;
            break;
          case kind::GT:
            newKind = kind::BITVECTOR_SGT;
            break;
          case kind::GEQ:
            newKind = kind::BITVECTOR_SGE;
            break;
          case kind::EQUAL:
          case kind::ITE:
            break;
          default:
            if (theory::Theory::theoryOf(current) == theory::THEORY_BOOL) {
              break;
            }
            throw TypeCheckingException(current.toExpr(), std::string("Cannot translate to BV: ") + current.toString());
        }
        for (unsigned i = 0; i < children.size(); ++i) {
          TypeNode type = children[i].getType();
          if (!type.isBitVector()) {
            continue;
          }
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize < max) {
            // sign extend
            Node signExtendOp = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(max - bvsize));
            children[i] = nm->mkNode(signExtendOp, children[i]);
          }
        }
      }
      NodeBuilder<> builder(newKind);
      for (unsigned i = 0; i < children.size(); ++i) {
        builder << children[i];
      }
      // Mark the substitution and continue
      Node result = builder;

      result = theory::Rewriter::rewrite(result);
      cache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // It's a leaf: could be a variable or a numeral
        Node result = current;
        if (current.isVar()) {
          if (current.getType() == nm->integerType()) {
            result = nm->mkSkolem("__intToBV_var", nm->mkBitVectorType(size),
                                  "Variable introduced in intToBV pass");
          }
          else {
            AlwaysAssert(current.getType() == nm->booleanType());
          }
        }
        else if (current.isConst()) {
          switch (current.getKind()) {
            case kind::CONST_RATIONAL: {
              Rational constant = current.getConst<Rational>();
              AlwaysAssert(constant.isIntegral());
              AlwaysAssert(constant >= 0);
              BitVector bv(size, constant.getNumerator());
              if (bv.toSignedInt() != constant.getNumerator()) {
                throw TypeCheckingException(current.toExpr(), std::string("Not enough bits for constant in intToBV: ") + current.toString());
              }
              result = nm->mkConst(bv);
              break;
            }
            case kind::CONST_BOOLEAN:
              break;
            default:
              throw TypeCheckingException(current.toExpr(), std::string("Cannot translate const to BV: ") + current.toString());
          }
        }
        else {
          throw TypeCheckingException(current.toExpr(), std::string("Cannot translate to BV: ") + current.toString());
        }
        cache[current] = result;
        toVisit.pop_back();
      }
    }
  }
  return cache[n_binary];
}

BitBlastModePass::BitBlastModePass() : PreprocessingPass("bitBlastMode", true){
}

void BitBlastModePass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_theoryEngine = theoryEngine;
} 

PreprocessingPassResult BitBlastModePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_theoryEngine->mkAckermanizationAsssertions(assertionsToPreprocess->ref());
 return PreprocessingPassResult(true);
}

BVAbstractionPass::BVAbstractionPass() : PreprocessingPass("bvAbstraction", true){
}

void BVAbstractionPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_smt = smt;
 d_theoryEngine = theoryEngine;
} 

void BVAbstractionPass::bvAbstraction(AssertionPipeline* assertionsToPreprocess){
  Trace("bv-abstraction") << "SmtEnginePrivate::bvAbstraction()" << std::endl;
  std::vector<Node> new_assertions;
  bool changed = d_theoryEngine->ppBvAbstraction(assertionsToPreprocess->ref(), new_assertions);
  //This method just changes the assertionToPreprocess, so the new_assertions variable is not necessary.
  //TODO: change how ppBvAbstraction works
  //order of rewrite also changed around 
 assertionsToPreprocess->ref().swap(new_assertions);
 // if we are using the lazy solver and the abstraction
  // applies, then UF symbols were introduced
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY &&
      changed) {
    LogicRequest req(*d_smt);
    req.widenLogic(theory::THEORY_UF);
  }
}
 
PreprocessingPassResult BVAbstractionPass::apply(AssertionPipeline* assertionsToPreprocess){
    dumpAssertions("pre-bv-abstraction", *assertionsToPreprocess);
    bvAbstraction(assertionsToPreprocess);
    dumpAssertions("post-bv-abstraction", *assertionsToPreprocess);
 return PreprocessingPassResult(true);
} 

UnconstrainedSimpPass::UnconstrainedSimpPass() : PreprocessingPass("unconstrainedSimp", true) {
}

void UnconstrainedSimpPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_theoryEngine = theoryEngine; 
} 

PreprocessingPassResult UnconstrainedSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
  TimerStat::CodeTimer unconstrainedSimpTimer(d_timer);
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << std::endl;
  d_theoryEngine->ppUnconstrainedSimp(assertionsToPreprocess->ref());
 return PreprocessingPassResult(true);
}

RewritePass::RewritePass() : PreprocessingPass("rewrite", true){
}

void RewritePass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 

PreprocessingPassResult RewritePass::apply(AssertionPipeline* assertionsToPreprocess){
   for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    assertionsToPreprocess->replace(i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
    }
 return PreprocessingPassResult(true);
}

NotUnsatCoresPass::NotUnsatCoresPass() : PreprocessingPass("notUnsatCores", true){
}

void NotUnsatCoresPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_topLevelSubstitutions = topLevelSubstitutions;
} 

PreprocessingPassResult NotUnsatCoresPass::apply(AssertionPipeline* assertionsToPreprocess){
  Chat() << "applying substitutions..." << std::endl;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                        << "applying substitutions" << std::endl;
      for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
        Trace("simplify") << "applying to " << (*assertionsToPreprocess)[i] << std::endl;
        spendResource(options::preprocessStep());
        assertionsToPreprocess->replace(i, theory::Rewriter::rewrite(d_topLevelSubstitutions->apply((*assertionsToPreprocess)[i])));
        Trace("simplify") << "  got " << (*assertionsToPreprocess)[i] << std::endl;
       }
 return PreprocessingPassResult(true);
}
     
BVToBoolPass::BVToBoolPass() : PreprocessingPass("bvToBool", true) {
}

void BVToBoolPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
  d_theoryEngine = theoryEngine;
} 

PreprocessingPassResult BVToBoolPass::apply(AssertionPipeline* assertionsToPreprocess){
  dumpAssertions("pre-bv-to-bool", *assertionsToPreprocess);
  Chat() << "...doing bvToBool..." << std::endl;
  bvToBool(assertionsToPreprocess);
  //A rewrite pass was formerly here that has been moved to after the dump
  dumpAssertions("post-bv-to-bool", *assertionsToPreprocess);
  Trace("smt") << "POST bvToBool" << std::endl;
 return PreprocessingPassResult(true);
}

void BVToBoolPass::bvToBool(AssertionPipeline* assertionsToPreprocess) {
  Trace("bv-to-bool") << "SmtEnginePrivate::bvToBool()" << std::endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBvToBool(assertionsToPreprocess->ref(), new_assertions);
  //This method just changes the assertionToPreprocess, so the new_assertions variable is not necessary.
  //TODO: change how ppBvToBool works
  //order of rewrite also changed around 
  assertionsToPreprocess->ref().swap(new_assertions);
}

BoolToBVPass::BoolToBVPass() : PreprocessingPass("boolTobv", true) {
}
 
void BoolToBVPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_theoryEngine = theoryEngine;
} 

void BoolToBVPass::boolToBv(AssertionPipeline* assertionsToPreprocess) {
  Trace("bool-to-bv") << "SmtEnginePrivate::boolToBv()" << std::endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBoolToBv(assertionsToPreprocess->ref(), new_assertions);
  //This method just changes the assertionToPreprocess, so the new_assertions variable is not necessary.
  // TODO: change how ppBooltoBv works
  //Order of rewrite also changed around  
  assertionsToPreprocess->ref().swap(new_assertions);
}

PreprocessingPassResult BoolToBVPass::apply(AssertionPipeline* assertionsToPreprocess){
    dumpAssertions("pre-bool-to-bv", *assertionsToPreprocess);
    Chat() << "...doing boolToBv..." << std::endl;
    boolToBv(assertionsToPreprocess);
    dumpAssertions("post-bool-to-bv", *assertionsToPreprocess);
    Trace("smt") << "POST boolToBv" << std::endl;
 return PreprocessingPassResult(true);
}

SepPreSkolemEmpPass::SepPreSkolemEmpPass() : PreprocessingPass("sepPreSkolem", true) {
}
 
void SepPreSkolemEmpPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 

PreprocessingPassResult SepPreSkolemEmpPass::apply(AssertionPipeline* assertionsToPreprocess){
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = theory::sep::TheorySepRewriter::preprocess( prev );
      if( next!=prev ){
        assertionsToPreprocess->replace(i, theory::Rewriter::rewrite( next ));
        Trace("sep-preprocess") << "*** Preprocess sep " << prev << std::endl;
        Trace("sep-preprocess") << "   ...got " << (*assertionsToPreprocess)[i] << std::endl;
       }
  }
 return PreprocessingPassResult(true);
}

QuantifiedPass::QuantifiedPass() : PreprocessingPass("quantified", true) { 
}

void QuantifiedPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_theoryEngine = theoryEngine;
 d_smt = smt;
} 

PreprocessingPassResult QuantifiedPass::apply(AssertionPipeline* assertionsToPreprocess){
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-quant-preprocess" << std::endl;

    dumpAssertions("pre-skolem-quant", *assertionsToPreprocess);
    //remove rewrite rules, apply pre-skolemization to existential quantifiers
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = theory::quantifiers::QuantifiersRewriter::preprocess( prev );
      if( next!=prev ){
        assertionsToPreprocess->replace(i, theory::Rewriter::rewrite( next ) );
        Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev <<std::endl;
        Trace("quantifiers-preprocess") << "   ...got " << (*assertionsToPreprocess)[i] << std::endl;
      }
    }
    dumpAssertions("post-skolem-quant", *assertionsToPreprocess);
    if( options::macrosQuant() ){
      //quantifiers macro expansion
      theory::quantifiers::QuantifierMacros qm( d_theoryEngine->getQuantifiersEngine() );
      bool success;
      do{
        success = qm.simplify( assertionsToPreprocess->ref(), true );
      }while( success );
      //finalize the definitions
      qm.finalizeDefinitions();
    }

    //fmf-fun : assume admissible functions, applying preprocessing reduction to FMF
    if( options::fmfFunWellDefined() ){
      theory::quantifiers::FunDefFmf fdf;
      Assert( d_smt->d_fmfRecFunctionsDefined!=NULL );
      //must carry over current definitions (for incremental)
      for( context::CDList<Node>::const_iterator fit = d_smt->d_fmfRecFunctionsDefined->begin();
           fit != d_smt->d_fmfRecFunctionsDefined->end(); ++fit ) {
        Node f = (*fit);
        Assert( d_smt->d_fmfRecFunctionsAbs.find( f )!= d_smt->d_fmfRecFunctionsAbs.end() );
        TypeNode ft = d_smt->d_fmfRecFunctionsAbs[f];
        fdf.d_sorts[f] = ft;
        std::map< Node, std::vector< Node > >::iterator fcit = d_smt->d_fmfRecFunctionsConcrete.find( f );
        Assert( fcit!= d_smt->d_fmfRecFunctionsConcrete.end() );
        for( unsigned j=0; j<fcit->second.size(); j++ ){
          fdf.d_input_arg_inj[f].push_back( fcit->second[j] );
        }
      }
      fdf.simplify(assertionsToPreprocess->ref());
      //must store new definitions (for incremental)
      for( unsigned i=0; i<fdf.d_funcs.size(); i++ ){
        Node f = fdf.d_funcs[i];
        d_smt->d_fmfRecFunctionsAbs[f] = fdf.d_sorts[f];
        d_smt->d_fmfRecFunctionsConcrete[f].clear();
        for( unsigned j=0; j<fdf.d_input_arg_inj[f].size(); j++ ){
          d_smt->d_fmfRecFunctionsConcrete[f].push_back( fdf.d_input_arg_inj[f][j] );
        }
        d_smt->d_fmfRecFunctionsDefined->push_back( f );
      }
    }
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-quant-preprocess" << std::endl;
 return PreprocessingPassResult(true);
}

InferenceOrFairnessPass::InferenceOrFairnessPass() : PreprocessingPass("inferenceOrFairness", true) {
}

void InferenceOrFairnessPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_theoryEngine = theoryEngine;
 d_smt = smt;
} 

PreprocessingPassResult InferenceOrFairnessPass::apply(AssertionPipeline* assertionsToPreprocess){
     //sort inference technique
    SortInference * si = d_theoryEngine->getSortInference();
    si->simplify( assertionsToPreprocess->ref(), options::sortInference(), options::ufssFairnessMonotone() );
    for( std::map< Node, Node >::iterator it = si->d_model_replace_f.begin(); it != si->d_model_replace_f.end(); ++it ){
      d_smt->setPrintFuncInModel( it->first.toExpr(), false );
      d_smt->setPrintFuncInModel( it->second.toExpr(), true );
    }
return PreprocessingPassResult(true);
}

PBRewritePass::PBRewritePass()  : PreprocessingPass("pbRewrite", true) {
}

void PBRewritePass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_pbsProcessor = pbsProcessor; 
} 

PreprocessingPassResult PBRewritePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_pbsProcessor->learn(assertionsToPreprocess->ref());
    if(d_pbsProcessor->likelyToHelp()){
      d_pbsProcessor->applyReplacements(assertionsToPreprocess->ref());
    }
 return PreprocessingPassResult(true);
}

RemoveITEPass::RemoveITEPass() : PreprocessingPass("removeITE", true) {
}

void RemoveITEPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_smt = smt;
 d_iteRemover = iteRemover; 
} 

PreprocessingPassResult RemoveITEPass::apply(AssertionPipeline* assertionsToPreprocess){
  d_smt->finalOptionsAreSet();
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::removeITEs()" << endl;

  // Remove all of the ITE occurrences and normalize
  d_iteRemover->run(assertionsToPreprocess->ref(), *assertionsToPreprocess->getSkolemMap(), true);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    assertionsToPreprocess->replace(i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
  }
 return PreprocessingPassResult(true);
}

DoStaticLearningPass::DoStaticLearningPass() : PreprocessingPass("doStaticLearning", true) {
}

void DoStaticLearningPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_smt = smt;
 d_theoryEngine = theoryEngine; 
} 

void DoStaticLearningPass::staticLearning(AssertionPipeline* assertionsToPreprocess){
  d_smt->finalOptionsAreSet();
  spendResource(options::preprocessStep());

  TimerStat::CodeTimer staticLearningTimer(d_timer);

  Trace("simplify") << "SmtEnginePrivate::staticLearning()" << std::endl;

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {

    NodeBuilder<> learned(kind::AND);
    learned << (*assertionsToPreprocess)[i];
    d_theoryEngine->ppStaticLearn((*assertionsToPreprocess)[i], learned);
    if(learned.getNumChildren() == 1) {
      learned.clear();
    } else {
      assertionsToPreprocess->replace(i, learned);
    }
  } 
}

PreprocessingPassResult DoStaticLearningPass::apply(AssertionPipeline* assertionsToPreprocess){
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-static-learning" << std::endl;
    // Perform static learning
    Chat() << "doing static learning..." << std::endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): "
                      << "performing static learning" << std::endl;
    staticLearning(assertionsToPreprocess);
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-static-learning" << std::endl;
 return PreprocessingPassResult(true);
} 

RewriteApplyToConstPass::RewriteApplyToConstPass(): PreprocessingPass("rewriteApplyToConst", true) {
}

void RewriteApplyToConstPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
} 

Node RewriteApplyToConstPass::rewriteApplyToConst(TNode n){
    NodeToNodeHashMap d_rewriteApplyToConstCache;
    Trace("rewriteApplyToConst") << "rewriteApplyToConst :: " << n << std::endl;

    if(n.getMetaKind() == kind::metakind::CONSTANT ||
       n.getMetaKind() == kind::metakind::VARIABLE ||
       n.getMetaKind() == kind::metakind::NULLARY_OPERATOR)
    {
      return n;
    }

    if(d_rewriteApplyToConstCache.find(n) != d_rewriteApplyToConstCache.end()) {
      Trace("rewriteApplyToConst") << "in cache :: "
                                   << d_rewriteApplyToConstCache[n]
                                   << std::endl;
      return d_rewriteApplyToConstCache[n];
    }

    if(n.getKind() == kind::APPLY_UF) {
      if(n.getNumChildren() == 1 && n[0].isConst() &&
         n[0].getType().isInteger())
      {
        std::stringstream ss;
        ss << n.getOperator() << "_";
        if(n[0].getConst<Rational>() < 0) {
          ss << "m" << -n[0].getConst<Rational>();
        } else {
          ss << n[0];
        }
        Node newvar = NodeManager::currentNM()->mkSkolem(
            ss.str(), n.getType(), "rewriteApplyToConst skolem",
            NodeManager::SKOLEM_EXACT_NAME);
        d_rewriteApplyToConstCache[n] = newvar;
        Trace("rewriteApplyToConst") << "made :: " << newvar << std::endl;
        return newvar;
      } else {
        std::stringstream ss;
        ss << "The rewrite-apply-to-const preprocessor is currently limited;"
           << std::endl
           << "it only works if all function symbols are unary and with Integer"
           << std::endl
           << "domain, and all applications are to integer values." << std::endl
           << "Found application: " << n;
        Unhandled(ss.str());
      }
    }
    NodeBuilder<> builder(n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      builder << n.getOperator();
    }
    for(unsigned i = 0; i < n.getNumChildren(); ++i) {
      builder << rewriteApplyToConst(n[i]);
    }
    Node rewr = builder;
    d_rewriteApplyToConstCache[n] = rewr;
    Trace("rewriteApplyToConst") << "built :: " << rewr << std::endl;
    return rewr;
}

PreprocessingPassResult RewriteApplyToConstPass::apply(AssertionPipeline* assertionsToPreprocess){
   Chat() << "Rewriting applies to constants..." << std::endl;
    TimerStat::CodeTimer codeTimer(d_timer);
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      (*assertionsToPreprocess)[i] = theory::Rewriter::rewrite(rewriteApplyToConst((*assertionsToPreprocess)[i]));
    }
 return PreprocessingPassResult(true);
}

TheoryPreprocessPass::TheoryPreprocessPass() : PreprocessingPass("theoryPreprocess", true) {
}

void TheoryPreprocessPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_theoryEngine = theoryEngine; 
} 

PreprocessingPassResult TheoryPreprocessPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "theory preprocessing..." << endl;
    TimerStat::CodeTimer codeTimer(d_timer);
    // Call the theory preprocessors
    d_theoryEngine->preprocessStart();
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      assertionsToPreprocess->replace(i, d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
    }
   return PreprocessingPassResult(true);
}

BitBlastModeEagerPass::BitBlastModeEagerPass() : PreprocessingPass("bitBlastModeEager", true) {
}

void BitBlastModeEagerPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_theoryEngine = theoryEngine; 
} 

PreprocessingPassResult BitBlastModeEagerPass::apply(AssertionPipeline* assertionsToPreprocess){
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
      TNode atom = (*assertionsToPreprocess)[i];
      Node eager_atom = NodeManager::currentNM()->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
      assertionsToPreprocess->replace(i, eager_atom);
      theory::TheoryModel* m = d_theoryEngine->getModel();
      m->addSubstitution(eager_atom, atom);
    }
 return PreprocessingPassResult(true);
}

NoConflictPass::NoConflictPass() : PreprocessingPass("noConflict", true) {
}

void NoConflictPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) {
 d_decisionEngine = decisionEngine; 
} 

PreprocessingPassResult NoConflictPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "pushing to decision engine..." << std::endl;
    //Assert moved to outside    
    d_decisionEngine->addAssertions
      (assertionsToPreprocess->ref(), assertionsToPreprocess->getRealAssertionsEnd(), *assertionsToPreprocess->getSkolemMap());
 return PreprocessingPassResult(true);
}

CNFPass::CNFPass() : PreprocessingPass("cnf", true) {
}

void CNFPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_propEngine = propEngine; 
} 

PreprocessingPassResult CNFPass::apply(AssertionPipeline* assertionsToPreprocess){
   Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_timer);
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      Chat() << "+ " << (*assertionsToPreprocess)[i] << std::endl;
      d_propEngine->assertFormula((*assertionsToPreprocess)[i]);
    }
  return PreprocessingPassResult(true);
}

RepeatSimpPass::RepeatSimpPass() :
    PreprocessingPass("repeatSimp", true) {
}

void RepeatSimpPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 d_topLevelSubstitutions = topLevelSubstitutions; 
} 

bool RepeatSimpPass::checkForBadSkolems(TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache, AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = assertionsToPreprocess->getSkolemMap()->find(n);
    bool bad = false;
    if (it != assertionsToPreprocess->getSkolemMap()->end()) {
      if (!((*it).first < n)) {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    if (checkForBadSkolems(n[k], skolem, cache, assertionsToPreprocess)) {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

void RepeatSimpPass::collectSkolems(TNode n, set<TNode>& skolemSet, unordered_map<Node, bool, NodeHashFunction>& cache, AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = assertionsToPreprocess->getSkolemMap()->find(n);
    if (it != assertionsToPreprocess->getSkolemMap()->end()) {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    collectSkolems(n[k], skolemSet, cache, assertionsToPreprocess);
  }
  cache[n] = true;
}


PreprocessingPassResult RepeatSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the order in which these variables were introduced
      // during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr mapped to by sk.

      // cache for expression traversal
      std::unordered_map<Node, bool, NodeHashFunction> cache;
      // First, find all skolems that appear in the substitution map - their associated iteExpr will need
      // to be moved to the main assertion set
      std::set<TNode> skolemSet;
      theory::SubstitutionMap::iterator pos = d_topLevelSubstitutions->begin();
      for (; pos != d_topLevelSubstitutions->end(); ++pos) {
        collectSkolems((*pos).first, skolemSet, cache, assertionsToPreprocess);
        collectSkolems((*pos).second, skolemSet, cache, assertionsToPreprocess);
      }

      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper assertion
      IteSkolemMap::iterator it = assertionsToPreprocess->getSkolemMap()->begin();
      IteSkolemMap::iterator iend = assertionsToPreprocess->getSkolemMap()->end();
      NodeBuilder<> builder(kind::AND);
      builder << (*assertionsToPreprocess)[assertionsToPreprocess->getRealAssertionsEnd() - 1];
      std::vector<TNode> toErase;
      for (; it != iend; ++it) {
        if (skolemSet.find((*it).first) == skolemSet.end()) {
          TNode iteExpr = (*assertionsToPreprocess)[(*it).second];
          if (iteExpr.getKind() == kind::ITE &&
              iteExpr[1].getKind() == kind::EQUAL &&
              iteExpr[1][0] == (*it).first &&
              iteExpr[2].getKind() == kind::EQUAL &&
              iteExpr[2][0] == (*it).first) {
            cache.clear();
            bool bad = checkForBadSkolems(iteExpr[0], (*it).first, cache, assertionsToPreprocess);
            bad = bad || checkForBadSkolems(iteExpr[1][1], (*it).first, cache, assertionsToPreprocess);
            bad = bad || checkForBadSkolems(iteExpr[2][1], (*it).first, cache, assertionsToPreprocess);
            if (!bad) {
              continue;
            }
          }
        }
        // Move this iteExpr into the main assertions
        builder << (*assertionsToPreprocess)[(*it).second];
        (*assertionsToPreprocess)[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
        toErase.push_back((*it).first);
      }
      if(builder.getNumChildren() > 1) {
        while (!toErase.empty()) {
          assertionsToPreprocess->getSkolemMap()->erase(toErase.back());
          toErase.pop_back();
        }
        (*assertionsToPreprocess)[assertionsToPreprocess->getRealAssertionsEnd() - 1] = theory::Rewriter::rewrite(Node(builder));
       }
 return PreprocessingPassResult(true);
}

NonClausalSimplificationPass::NonClausalSimplificationPass() :
   PreprocessingPass("nonClausalSimplification", true), d_numConstantProps("preproc::d_numConstantProps", 0) {
}

void NonClausalSimplificationPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){
 smtStatisticsRegistry()->registerStat(&d_numConstantProps);
 d_smt = smt;
 d_propagatorNeedsFinish = propagatorNeedsFinish;
 d_propagator = propagator;
 d_substitutionsIndex = substitutionsIndex;
 d_topLevelSubstitutions = topLevelSubstitutions;
 d_nonClausalLearnedLiterals = nonClausalLearnedLiterals;
}

// returns false if it learns a conflict
PreprocessingPassResult NonClausalSimplificationPass::apply(AssertionPipeline* assertionsToPreprocess) {
  spendResource(options::preprocessStep());
  d_smt->finalOptionsAreSet();

  if(options::unsatCores() || options::fewerPreprocessingHoles()) {
    return PreprocessingPassResult(true);
  }

  TimerStat::CodeTimer nonclausalTimer(d_timer);

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify()" << endl;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    Trace("simplify") << "Assertion #" << i << " : " << (*assertionsToPreprocess)[i] << std::endl;
  }

  if(*d_propagatorNeedsFinish) {
    d_propagator->finish();
    *d_propagatorNeedsFinish = false;
  }
  d_propagator->initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    Assert(Rewriter::rewrite((*assertionsToPreprocess)[i]) == (*assertionsToPreprocess)[i]);
    // Don't reprocess substitutions
    if (*d_substitutionsIndex > 0 && i == *d_substitutionsIndex) {
      continue;
    }
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting " << (*assertionsToPreprocess)[i] << endl;
    Debug("cores") << "d_propagator assertTrue: " << (*assertionsToPreprocess)[i] << std::endl;
    d_propagator->assertTrue((*assertionsToPreprocess)[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (d_propagator->propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    assertionsToPreprocess->clear();
    addFormula(falseNode, false, assertionsToPreprocess, false) ;
    *d_propagatorNeedsFinish = true;
    return PreprocessingPassResult(false);
  }


  Trace("simplify") << "Iterate through " << d_nonClausalLearnedLiterals->size() << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  theory::SubstitutionMap constantPropagations(d_smt->d_context);
  theory::SubstitutionMap newSubstitutions(d_smt->d_context);
  theory::SubstitutionMap::iterator pos;
  unsigned j = 0;
  for(unsigned i = 0, i_end = d_nonClausalLearnedLiterals->size(); i < i_end; ++ i) {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = (*d_nonClausalLearnedLiterals)[i];
    Assert(theory::Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(d_topLevelSubstitutions->apply(learnedLiteral) == learnedLiteral);
    Trace("simplify") << "Process learnedLiteral : " << learnedLiteral << std::endl;
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew) {
      learnedLiteral = theory::Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after newSubs : " << learnedLiteral << std::endl;
    for (;;) {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral) {
        break;
      }
      ++d_numConstantProps;
      learnedLiteral = theory::Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after constProp : " << learnedLiteral << std::endl;
    // It might just simplify to a constant
    if (learnedLiteral.isConst()) {
      if (learnedLiteral.getConst<bool>()) {
        // If the learned literal simplifies to true, it's redundant
        continue;
      } else {
        // If the learned literal simplifies to false, we're in conflict
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict with "
                          << (*d_nonClausalLearnedLiterals)[i] << endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, assertionsToPreprocess, false);
        *d_propagatorNeedsFinish = true;
        return PreprocessingPassResult(false);
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "solving " << learnedLiteral << endl;

    theory::Theory::PPAssertStatus solveStatus =
      d_smt->d_theoryEngine->solve(learnedLiteral, newSubstitutions);

    switch (solveStatus) {
      case theory::Theory::PP_ASSERT_STATUS_SOLVED: {
        // The literal should rewrite to true
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "solved " << learnedLiteral << endl;
        Assert(theory::Rewriter::rewrite(newSubstitutions.apply(learnedLiteral)).isConst());
        //        vector<pair<Node, Node> > equations;
        //        constantPropagations.simplifyLHS(d_topLevelSubstitutions, equations, true);
        //        if (equations.empty()) {
        //          break;
        //        }
        //        Assert(equations[0].first.isConst() && equations[0].second.isConst() && equations[0].first != equations[0].second);
        // else fall through
        break;
      }
      case theory::Theory::PP_ASSERT_STATUS_CONFLICT:
        // If in conflict, we return false
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict while solving "
                          << learnedLiteral << endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false,assertionsToPreprocess, false);
        *d_propagatorNeedsFinish = true;
        return PreprocessingPassResult(false);
      default:
        //removed d_doConstantProp
        if (learnedLiteral.getKind() == kind::EQUAL && (learnedLiteral[0].isConst() || learnedLiteral[1].isConst())) {
          // constant propagation
          TNode t;
          TNode c;
          if (learnedLiteral[0].isConst()) {
            t = learnedLiteral[1];
            c = learnedLiteral[0];
          }
          else {
            t = learnedLiteral[0];
            c = learnedLiteral[1];
          }
          Assert(!t.isConst());
          Assert(constantPropagations.apply(t) == t);
          Assert(d_topLevelSubstitutions->apply(t) == t);
          Assert(newSubstitutions.apply(t) == t);
          constantPropagations.addSubstitution(t, c);
          // vector<pair<Node,Node> > equations;
          // constantPropagations.simplifyLHS(t, c, equations, true);
          // if (!equations.empty()) {
          //   Assert(equations[0].first.isConst() && equations[0].second.isConst() && equations[0].first != equations[0].second);
          //   d_assertions.clear();
          //   addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false);
          //   return;
          // }
          // d_topLevelSubstitutions.simplifyRHS(constantPropagations);
        }
        else {
          // Keep the literal
          (*d_nonClausalLearnedLiterals)[j++] = (*d_nonClausalLearnedLiterals)[i];
        }
        break;
    }
  }

#ifdef CVC4_ASSERTIONS
  // NOTE: When debugging this code, consider moving this check inside of the
  // loop over d_nonClausalLearnedLiterals. This check has been moved outside
  // because it is costly for certain inputs (see bug 508).
  //
  // Check data structure invariants:
  // 1. for each lhs of d_topLevelSubstitutions, does not appear anywhere in rhs of d_topLevelSubstitutions or anywhere in constantPropagations
  // 2. each lhs of constantPropagations rewrites to itself
  // 3. if l -> r is a constant propagation and l is a subterm of l' with l' -> r' another constant propagation, then l'[l/r] -> r' should be a
  //    constant propagation too
  // 4. each lhs of constantPropagations is different from each rhs
  for (pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos) {
    Assert((*pos).first.isVar());
    Assert(d_topLevelSubstitutions->apply((*pos).first) == (*pos).first);
    Assert(d_topLevelSubstitutions->apply((*pos).second) == (*pos).second);
    Assert(newSubstitutions.apply(newSubstitutions.apply((*pos).second)) == newSubstitutions.apply((*pos).second));
  }
  for (pos = constantPropagations.begin(); pos != constantPropagations.end(); ++pos) {
    Assert((*pos).second.isConst());
    Assert(theory::Rewriter::rewrite((*pos).first) == (*pos).first);
    // Node newLeft = d_topLevelSubstitutions.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) && constantPropagations.apply(newLeft) == (*pos).second));
    // }
    // newLeft = constantPropagations.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) && constantPropagations.apply(newLeft) == (*pos).second));
    // }
    Assert(constantPropagations.apply((*pos).second) == (*pos).second);
  }
 #endif  //CVC4_ASSERTIONS 

  // Resize the learnt
  Trace("simplify") << "Resize non-clausal learned literals to " << j << std::endl;
  d_nonClausalLearnedLiterals->resize(j);

  unordered_set<TNode, TNodeHashFunction> s;
  Trace("debugging") << "NonClausal simplify pre-preprocess\n";
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    Node assertion = (*assertionsToPreprocess)[i];
    Node assertionNew = newSubstitutions.apply(assertion);
    Trace("debugging") << "assertion = " << assertion << endl;
    Trace("debugging") << "assertionNew = " << assertionNew << endl;
    if (assertion != assertionNew) {
      assertion = theory::Rewriter::rewrite(assertionNew);
      Trace("debugging") << "rewrite(assertion) = " << assertion << endl;
    }
    Assert(theory::Rewriter::rewrite(assertion) == assertion);
    for (;;) {
      assertionNew = constantPropagations.apply(assertion);
      if (assertionNew == assertion) {
        break;
      }
      ++d_numConstantProps;
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
      assertion = theory::Rewriter::rewrite(assertionNew);
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
    }
    Trace("debugging") << "\n";
    s.insert(assertion);
    assertionsToPreprocess->replace(i, assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: "
                      << assertion << endl;
  }

  // If in incremental mode, add substitutions to the list of assertions
  if (*d_substitutionsIndex > 0) {
    NodeBuilder<> substitutionsBuilder(kind::AND);
    substitutionsBuilder << (*assertionsToPreprocess)[*d_substitutionsIndex];
    pos = newSubstitutions.begin();
    for (; pos != newSubstitutions.end(); ++pos) {
      // Add back this substitution as an assertion
      TNode lhs = (*pos).first, rhs = newSubstitutions.apply((*pos).second);
      Node n = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
      substitutionsBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will notify SAT layer of substitution: " << n << endl;
    }
    if (substitutionsBuilder.getNumChildren() > 1) {
      assertionsToPreprocess->replace(*d_substitutionsIndex,
        theory::Rewriter::rewrite(Node(substitutionsBuilder)));
    }
  } else {
    // If not in incremental mode, must add substitutions to model
    theory::TheoryModel* m = d_smt->d_theoryEngine->getModel();
    if(m != NULL) {
      for(pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos) {
        Node n = (*pos).first;
        Node v = newSubstitutions.apply((*pos).second);
        Trace("model") << "Add substitution : " << n << " " << v << endl;
        m->addSubstitution( n, v );
      }
    }
  }

  NodeBuilder<> learnedBuilder(kind::AND);
  Assert(assertionsToPreprocess->getRealAssertionsEnd() <= assertionsToPreprocess->size());
  learnedBuilder << (*assertionsToPreprocess)[assertionsToPreprocess->getRealAssertionsEnd() - 1];

  for (unsigned i = 0; i < d_nonClausalLearnedLiterals->size(); ++ i) {
    Node learned = (*d_nonClausalLearnedLiterals)[i];
    Assert(d_topLevelSubstitutions->apply(learned) == learned);
    Node learnedNew = newSubstitutions.apply(learned);
    if (learned != learnedNew) {
      learned = theory::Rewriter::rewrite(learnedNew);
    }
    Assert(theory::Rewriter::rewrite(learned) == learned);
    for (;;) {
      learnedNew = constantPropagations.apply(learned);
      if (learnedNew == learned) {
        break;
      }
      ++d_numConstantProps;
      learned = theory::Rewriter::rewrite(learnedNew);
    }
    if (s.find(learned) != s.end()) {
      continue;
    }
    s.insert(learned);
    learnedBuilder << learned;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal learned : "
                      << learned << endl;
  }
  d_nonClausalLearnedLiterals->clear();

  for (pos = constantPropagations.begin(); pos != constantPropagations.end(); ++pos) {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(d_topLevelSubstitutions->apply(cProp) == cProp);
    Node cPropNew = newSubstitutions.apply(cProp);
    if (cProp != cPropNew) {
      cProp = theory::Rewriter::rewrite(cPropNew);
      Assert(theory::Rewriter::rewrite(cProp) == cProp);
    }
    if (s.find(cProp) != s.end()) {
      continue;
    }
    s.insert(cProp);
    learnedBuilder << cProp;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal constant propagation : "
                      << cProp << endl;
  }

  // Add new substitutions to topLevelSubstitutions
  // Note that we don't have to keep rhs's in full solved form
  // because SubstitutionMap::apply does a fixed-point iteration when substituting
  d_topLevelSubstitutions->addSubstitutions(newSubstitutions);

  if(learnedBuilder.getNumChildren() > 1) {
    assertionsToPreprocess->replace(assertionsToPreprocess->getRealAssertionsEnd() - 1,
      theory::Rewriter::rewrite(Node(learnedBuilder)));
  }

  *d_propagatorNeedsFinish = true;
  return PreprocessingPassResult(true);
}
MiplibTrickPass::MiplibTrickPass() :
   PreprocessingPass("miplibTrick", true), d_numMiplibAssertionsRemoved("preproc::d_numMiplibAssertionsRemoved", 0), d_fakeContext() {
}

void MiplibTrickPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals){

 smtStatisticsRegistry()->registerStat(&d_numMiplibAssertionsRemoved); d_smt = smt; d_propagator = propagator; d_boolVars = boolVars;
 d_topLevelSubstitutions = topLevelSubstitutions;
}

size_t MiplibTrickPass::removeFromConjunction(Node& n, const std::unordered_set<unsigned long>& toRemove) {
  Assert(n.getKind() == kind::AND);
  size_t removals = 0;
  for(Node::iterator j = n.begin(); j != n.end(); ++j) {
    size_t subremovals = 0;
    Node sub = *j;
    if(toRemove.find(sub.getId()) != toRemove.end() ||
       (sub.getKind() == kind::AND && (subremovals = removeFromConjunction(sub, toRemove)) > 0)) {
      NodeBuilder<> b(kind::AND);
      b.append(n.begin(), j);
      if(subremovals > 0) {
        removals += subremovals;
        b << sub;
      } else {
        ++removals;
      }
      for(++j; j != n.end(); ++j) {
        if(toRemove.find((*j).getId()) != toRemove.end()) {
          ++removals;
        } else if((*j).getKind() == kind::AND) {
          sub = *j;
          if((subremovals = removeFromConjunction(sub, toRemove)) > 0) {
            removals += subremovals;
            b << sub;
          } else {
            b << *j;
          }
        } else {
          b << *j;
        }
      }
      if(b.getNumChildren() == 0) {
        n = NodeManager::currentNM()->mkConst(true);
        b.clear();
      } else if(b.getNumChildren() == 1) {
        n = b[0];
        b.clear();
      } else {
        n = b;
      }
      n = Rewriter::rewrite(n);
      return removals;
    }
  }

  Assert(removals == 0);
  return 0;
}


void MiplibTrickPass::traceBackToAssertions(const std::vector<Node>& nodes, std::vector<TNode>& assertions) {
  const booleans::CircuitPropagator::BackEdgesMap& backEdges = d_propagator->getBackEdges();
  for(vector<Node>::const_iterator i = nodes.begin(); i != nodes.end(); ++i) {
    booleans::CircuitPropagator::BackEdgesMap::const_iterator j = backEdges.find(*i);
    // term must appear in map, otherwise how did we get here?!
    Assert(j != backEdges.end());
    // if term maps to empty, that means it's a top-level assertion
    if(!(*j).second.empty()) {
      traceBackToAssertions((*j).second, assertions);
    } else {
      assertions.push_back(*i);
    }
  }
}

void MiplibTrickPass::doMiplibTrick(AssertionPipeline* assertionsToPreprocess) {
  Assert(assertionsToPreprocess->getRealAssertionsEnd() == assertionsToPreprocess->size());
  Assert(!options::incrementalSolving());

  const theory::booleans::CircuitPropagator::BackEdgesMap& backEdges = d_propagator->getBackEdges();
  unordered_set<unsigned long> removeAssertions;

  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(Rational(0)), one = nm->mkConst(Rational(1));

  unordered_map<TNode, Node, TNodeHashFunction> intVars;
  for(vector<Node>::const_iterator i = d_boolVars->begin(); i != d_boolVars->end(); ++i) {
    if(d_propagator->isAssigned(*i)) {
      Debug("miplib") << "ineligible: " << *i << " because assigned " << d_propagator->getAssignment(*i) << endl;
      continue;
    }

    vector<TNode> assertions;
    theory::booleans::CircuitPropagator::BackEdgesMap::const_iterator j = backEdges.find(*i);
    // if not in back edges map, the bool var is unconstrained, showing up in no assertions.
    // if maps to an empty vector, that means the bool var was asserted itself.
    if(j != backEdges.end()) {
      if(!(*j).second.empty()) {
        traceBackToAssertions((*j).second, assertions);
      } else {
        assertions.push_back(*i);
      }
    }
    Debug("miplib") << "for " << *i << endl;
    bool eligible = true;
    map<pair<Node, Node>, uint64_t> marks;
    map<pair<Node, Node>, vector<Rational> > coef;
    map<pair<Node, Node>, vector<Rational> > checks;
    map<pair<Node, Node>, vector<TNode> > asserts;
    for(vector<TNode>::const_iterator j = assertions.begin(); j != assertions.end(); ++j) {
      Debug("miplib") << "  found: " << *j << endl;
      if((*j).getKind() != kind::IMPLIES) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not =>)" << endl;
        break;
      }
      Node conj = BooleanSimplification::simplify((*j)[0]);
      if(conj.getKind() == kind::AND && conj.getNumChildren() > 6) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (N-ary /\\ too big)" << endl;
        break;
      }
      if(conj.getKind() != kind::AND && !conj.isVar() && !(conj.getKind() == kind::NOT && conj[0].isVar())) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not /\\ or literal)" << endl;
        break;
      }
      if((*j)[1].getKind() != kind::EQUAL ||
         !( ( (*j)[1][0].isVar() &&
              (*j)[1][1].getKind() == kind::CONST_RATIONAL ) ||
            ( (*j)[1][0].getKind() == kind::CONST_RATIONAL &&
              (*j)[1][1].isVar() ) )) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (=> (and X X) X)" << endl;
        break;
      }
      if(conj.getKind() == kind::AND) {
        vector<Node> posv;
        bool found_x = false;
        map<TNode, bool> neg;
        for(Node::iterator ii = conj.begin(); ii != conj.end(); ++ii) {
          if((*ii).isVar()) {
            posv.push_back(*ii);
            neg[*ii] = false;
            found_x = found_x || *i == *ii;
          } else if((*ii).getKind() == kind::NOT && (*ii)[0].isVar()) {
            posv.push_back((*ii)[0]);
            neg[(*ii)[0]] = true;
            found_x = found_x || *i == (*ii)[0];
          } else {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (non-var: " << *ii << ")" << endl;
            break;
          }
          if(d_propagator->isAssigned(posv.back())) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (" << posv.back() << " asserted)" << endl;
            break;
          }
        }
        if(!eligible) {
          break;
        }
        if(!found_x) {
          eligible = false;
          Debug("miplib") << "  --INELIGIBLE -- (couldn't find " << *i << " in conjunction)" << endl;
          break;
        }
        sort(posv.begin(), posv.end());
        const Node pos = NodeManager::currentNM()->mkNode(kind::AND, posv);
        const TNode var = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][1] : (*j)[1][0];
        const pair<Node, Node> pos_var(pos, var);
        const Rational& constant = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][0].getConst<Rational>() : (*j)[1][1].getConst<Rational>();
        uint64_t mark = 0;
        unsigned countneg = 0, thepos = 0;
        for(unsigned ii = 0; ii < pos.getNumChildren(); ++ii) {
          if(neg[pos[ii]]) {
            ++countneg;
          } else {
            thepos = ii;
            mark |= (0x1 << ii);
          }
        }
        if((marks[pos_var] & (1lu << mark)) != 0) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        Debug("miplib") << "mark is " << mark << " -- " << (1lu << mark) << endl;
        marks[pos_var] |= (1lu << mark);
        Debug("miplib") << "marks[" << pos << "," << var << "] now " << marks[pos_var] << endl;
        if(countneg == pos.getNumChildren()) {
          if(constant != 0) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        } else if(countneg == pos.getNumChildren() - 1) {
          Assert(coef[pos_var].size() <= 6 && thepos < 6);
          if(coef[pos_var].size() <= thepos) {
            coef[pos_var].resize(thepos + 1);
          }
          coef[pos_var][thepos] = constant;
        } else {
          if(checks[pos_var].size() <= mark) {
            checks[pos_var].resize(mark + 1);
          }
          checks[pos_var][mark] = constant;
        }
        asserts[pos_var].push_back(*j);
      } else {
        TNode x = conj;
        if(x != *i && x != (*i).notNode()) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (x not present where I expect it)" << endl;
          break;
        }
        const bool xneg = (x.getKind() == kind::NOT);
        x = xneg ? x[0] : x;
        Debug("miplib") << "  x:" << x << "  " << xneg << endl;
        const TNode var = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][1] : (*j)[1][0];
        const pair<Node, Node> x_var(x, var);
        const Rational& constant = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][0].getConst<Rational>() : (*j)[1][1].getConst<Rational>();
        unsigned mark = (xneg ? 0 : 1);
        if((marks[x_var] & (1u << mark)) != 0) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        marks[x_var] |= (1u << mark);
        if(xneg) {
          if(constant != 0) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        } else {
          Assert(coef[x_var].size() <= 6);
          coef[x_var].resize(6);
          coef[x_var][0] = constant;
        }
        asserts[x_var].push_back(*j);
      }
    }
    if(eligible) {
      for(map<pair<Node, Node>, uint64_t>::const_iterator j = marks.begin(); j != marks.end(); ++j) {
        const TNode pos = (*j).first.first;
        const TNode var = (*j).first.second;
        const pair<Node, Node>& pos_var = (*j).first;
        const uint64_t mark = (*j).second;
        const unsigned numVars = pos.getKind() == kind::AND ? pos.getNumChildren() : 1;
        uint64_t expected = (uint64_t(1) << (1 << numVars)) - 1;
        expected = (expected == 0) ? -1 : expected; // fix for overflow
        Debug("miplib") << "[" << pos << "] => " << hex << mark << " expect " << expected << dec << endl;
        Assert(pos.getKind() == kind::AND || pos.isVar());
        if(mark != expected) {
          Debug("miplib") << "  -- INELIGIBLE " << pos << " -- (insufficiently marked, got " << mark << " for " << numVars << " vars, expected " << expected << endl;
        } else {
          if(mark != 3) { // exclude single-var case; nothing to check there
            uint64_t sz = (uint64_t(1) << checks[pos_var].size()) - 1;
            sz = (sz == 0) ? -1 : sz; // fix for overflow
            Assert(sz == mark, "expected size %u == mark %u", sz, mark);
            for(size_t k = 0; k < checks[pos_var].size(); ++k) {
              if((k & (k - 1)) != 0) {
                Rational sum = 0;
                Debug("miplib") << k << " => " << checks[pos_var][k] << endl;
                for(size_t v = 1, kk = k; kk != 0; ++v, kk >>= 1) {
                  if((kk & 0x1) == 1) {
                    Assert(pos.getKind() == kind::AND);
                    Debug("miplib") << "var " << v << " : " << pos[v - 1] << " coef:" << coef[pos_var][v - 1] << endl;
                    sum += coef[pos_var][v - 1];
                  }
                }
                Debug("miplib") << "checkSum is " << sum << " input says " << checks[pos_var][k] << endl;
                if(sum != checks[pos_var][k]) {
                  eligible = false;
                  Debug("miplib") << "  -- INELIGIBLE " << pos << " -- (nonlinear combination)" << endl;
                  break;
                }
              } else {
                Assert(checks[pos_var][k] == 0, "checks[(%s,%s)][%u] should be 0, but it's %s", pos.toString().c_str(), var.toString().c_str(), k, checks[pos_var][k].toString().c_str()); // we never set for single-positive-var
              }
            }
          }
          if(!eligible) {
            eligible = true; // next is still eligible
            continue;
          }

          Debug("miplib") << "  -- ELIGIBLE " << *i << " , " << pos << " --" << endl;
          vector<Node> newVars;
          expr::NodeSelfIterator ii, iiend;
          if(pos.getKind() == kind::AND) {
            ii = pos.begin();
            iiend = pos.end();
          } else {
            ii = expr::NodeSelfIterator::self(pos);
            iiend = expr::NodeSelfIterator::selfEnd(pos);
          }
          for(; ii != iiend; ++ii) {
            Node& varRef = intVars[*ii];
            if(varRef.isNull()) {
              stringstream ss;
              ss << "mipvar_" << *ii;
              Node newVar = nm->mkSkolem(ss.str(), nm->integerType(), "a variable introduced due to scrubbing a miplib encoding", NodeManager::SKOLEM_EXACT_NAME);
              Node geq = theory::Rewriter::rewrite(nm->mkNode(kind::GEQ, newVar, zero));
              Node leq = theory::Rewriter::rewrite(nm->mkNode(kind::LEQ, newVar, one));
              addFormula(theory::Rewriter::rewrite(geq.andNode(leq)), false, assertionsToPreprocess, false);
              SubstitutionMap nullMap(&d_fakeContext);
              theory::Theory::PPAssertStatus status CVC4_UNUSED; // just for assertions
              status = d_smt->d_theoryEngine->solve(geq, nullMap); Assert(status == theory::Theory::PP_ASSERT_STATUS_UNSOLVED,
                     "unexpected solution from arith's ppAssert()");
              Assert(nullMap.empty(),
                     "unexpected substitution from arith's ppAssert()");
              status = d_smt->d_theoryEngine->solve(leq, nullMap);
              Assert(status == theory::Theory::PP_ASSERT_STATUS_UNSOLVED,
                     "unexpected solution from arith's ppAssert()");
              Assert(nullMap.empty(),
                     "unexpected substitution from arith's ppAssert()");
              d_smt->d_theoryEngine->getModel()->addSubstitution(*ii, newVar.eqNode(one));
              newVars.push_back(newVar);
              varRef = newVar;
            } else {
              newVars.push_back(varRef);
            }
            if(!d_smt->d_logic.areIntegersUsed()) {
              d_smt->d_logic = d_smt->d_logic.getUnlockedCopy();
              d_smt->d_logic.enableIntegers();
              d_smt->d_logic.lock();
            }
          }
          Node sum;
          if(pos.getKind() == kind::AND) {
            NodeBuilder<> sumb(kind::PLUS);
            for(size_t ii = 0; ii < pos.getNumChildren(); ++ii) {
              sumb << nm->mkNode(kind::MULT, nm->mkConst(coef[pos_var][ii]), newVars[ii]);
            }
            sum = sumb;
          } else {
            sum = nm->mkNode(kind::MULT, nm->mkConst(coef[pos_var][0]), newVars[0]);
          }
          Debug("miplib") << "vars[] " << var << endl
                          << "    eq " << theory::Rewriter::rewrite(sum) << endl;
          Node newAssertion = var.eqNode(theory::Rewriter::rewrite(sum));
          if(d_topLevelSubstitutions->hasSubstitution(newAssertion[0])) {
            //Warning() << "RE-SUBSTITUTION " << newAssertion[0] << endl;
            //Warning() << "REPLACE         " << newAssertion[1] << endl;
            //Warning() << "ORIG            " << d_topLevelSubstitutions.getSubstitution(newAssertion[0]) << endl;
            Assert(d_topLevelSubstitutions->getSubstitution(newAssertion[0]) == newAssertion[1]);
          } else if(pos.getNumChildren() <= options::arithMLTrickSubstitutions()) {
            d_topLevelSubstitutions->addSubstitution(newAssertion[0], newAssertion[1]);
            Debug("miplib") << "addSubs: " << newAssertion[0] << " to " << newAssertion[1] << endl;
          } else {
            Debug("miplib") << "skipSubs: " << newAssertion[0] << " to " << newAssertion[1] << " (threshold is " << options::arithMLTrickSubstitutions() << ")" << endl;
          }
          newAssertion = theory::Rewriter::rewrite(newAssertion);
          Debug("miplib") << "  " << newAssertion << endl;
          addFormula(newAssertion, false, assertionsToPreprocess, false);
          Debug("miplib") << "  assertions to remove: " << endl;
          for(vector<TNode>::const_iterator k = asserts[pos_var].begin(), k_end = asserts[pos_var].end(); k != k_end; ++k) {
            Debug("miplib") << "    " << *k << endl;
            removeAssertions.insert((*k).getId());
          }
        }
      }
    }
  }
  if(!removeAssertions.empty()) {
    Debug("miplib") << "SmtEnginePrivate::simplify(): scrubbing miplib encoding..." << endl;
    for(size_t i = 0; i < assertionsToPreprocess->getRealAssertionsEnd(); ++i) {
      if(removeAssertions.find((*assertionsToPreprocess)[i].getId()) != removeAssertions.end()) {
        Debug("miplib") << "SmtEnginePrivate::simplify(): - removing " << (*assertionsToPreprocess)[i] << endl;
        (*assertionsToPreprocess)[i] = NodeManager::currentNM()->mkConst(true);
        ++d_numMiplibAssertionsRemoved;
      } else if((*assertionsToPreprocess)[i].getKind() == kind::AND) {
        size_t removals = removeFromConjunction((*assertionsToPreprocess)[i], removeAssertions);
        if(removals > 0) {
          Debug("miplib") << "SmtEnginePrivate::simplify(): - reduced " << (*assertionsToPreprocess)[i] << endl;
          Debug("miplib") << "SmtEnginePrivate::simplify(): -      by " << removals << " conjuncts" << endl;
          d_numMiplibAssertionsRemoved += removals;
        }
      }
      Debug("miplib") << "had: " << (*assertionsToPreprocess)[i] << endl;
      (*assertionsToPreprocess)[i] = theory::Rewriter::rewrite(d_topLevelSubstitutions->apply((*assertionsToPreprocess)[i]));
      Debug("miplib") << "now: " << (*assertionsToPreprocess)[i] << endl;
    }
  } else {
    Debug("miplib") << "SmtEnginePrivate::simplify(): miplib pass found nothing." << endl;
  }
  assertionsToPreprocess->setRealAssertionsEnd(assertionsToPreprocess->size());
}

PreprocessingPassResult MiplibTrickPass::apply(AssertionPipeline* assertionsToPreprocess){
  Chat() << "...fixing miplib encodings..." << endl;
  Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "looking for miplib pseudobooleans..." << endl;
  TimerStat::CodeTimer miplibTimer(d_timer);
  doMiplibTrick(assertionsToPreprocess);
  return PreprocessingPassResult(true);       
}

EarlyTheoryPass::EarlyTheoryPass() : PreprocessingPass("earlyTheory", true) {
}

void EarlyTheoryPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) { 
 d_theoryEngine = theoryEngine;
}

PreprocessingPassResult EarlyTheoryPass::apply(AssertionPipeline* assertionsToPreprocess) {
   Chat() << "...doing early theory preprocessing..." << endl;
      TimerStat::CodeTimer codeTimer(d_timer);
      // Call the theory preprocessors
      d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
        Assert(Rewriter::rewrite((*assertionsToPreprocess)[i]) == (*assertionsToPreprocess)[i]);
        assertionsToPreprocess->replace(i, d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
        Assert(Rewriter::rewrite((*assertionsToPreprocess)[i]) == (*assertionsToPreprocess)[i]);
      }
  return PreprocessingPassResult(true);
}

SimpITEPass::SimpITEPass() : PreprocessingPass("simpITE", true) {
}
 
void SimpITEPass::initInternal(
     SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) { 
 d_theoryEngine = theoryEngine; 
}

void SimpITEPass::compressBeforeRealAssertions(size_t before, AssertionPipeline* assertionsToPreprocess){
  size_t curr = assertionsToPreprocess->size();
  if(before >= curr ||
     assertionsToPreprocess->getRealAssertionsEnd() <= 0 ||
     assertionsToPreprocess->getRealAssertionsEnd() >= curr){
    return;
  }
}

PreprocessingPassResult SimpITEPass::apply(AssertionPipeline* assertionsToPreprocess) {
  TimerStat::CodeTimer simpITETimer(d_timer);

  spendResource(options::preprocessStep());

  Trace("simplify") << "SmtEnginePrivate::simpITE()" << endl;

  unsigned numAssertionOnEntry = assertionsToPreprocess->size();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    spendResource(options::preprocessStep());
    Node result = d_theoryEngine->ppSimpITE((*assertionsToPreprocess)[i]);
    assertionsToPreprocess->replace(i, result);
    if(result.isConst() && !result.getConst<bool>()){
      return PreprocessingPassResult(false);
    }
  }
  bool result = d_theoryEngine->donePPSimpITE(assertionsToPreprocess->ref());
  if(numAssertionOnEntry < assertionsToPreprocess->size()){
    compressBeforeRealAssertions(numAssertionOnEntry, assertionsToPreprocess);
  }
  return PreprocessingPassResult(result);
}

}  // namespace preproc
}  // namespace CVC4
