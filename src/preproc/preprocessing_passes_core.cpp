#include "preproc/preprocessing_passes_core.h"

#include <ext/hash_map>
#include <string>
#include <stack>
#include "expr/node_manager_attributes.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/macros.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/sep/theory_sep_rewriter.h"
#include "theory/theory_model.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/bv_bitblast_mode.h"
#include "options/bv_options.h"
#include "options/uf_options.h"
#include "options/proof_options.h"
#include "util/ntuple.h"

using namespace std;

namespace CVC4 {
namespace preproc {

ExpandingDefinitionsPass::ExpandingDefinitionsPass(ResourceManager* resourceManager, SmtEngine* smt, TimerStat definitionExpansionTime) : PreprocessingPass(resourceManager), d_smt(smt), d_definitionExpansionTime(definitionExpansionTime){
}

Node ExpandingDefinitionsPass::expandDefinitions(TNode n, hash_map<Node, Node, NodeHashFunction>& cache, bool expandOnly)
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
      hash_map<Node, Node, NodeHashFunction>::iterator cacheHit = cache.find(n);
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
    }
  } while(!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

PreprocessingPassResult ExpandingDefinitionsPass::apply(AssertionPipeline* assertionsToPreprocess){
  Chat() << "expanding definitions..." << std::endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_definitionExpansionTime);
    hash_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      assertionsToPreprocess->replace(i, expandDefinitions((*assertionsToPreprocess)[i], cache));
    }
  return PreprocessingPassResult(true);
}

NlExtPurifyPass::NlExtPurifyPass(ResourceManager* resourceManager) :
    PreprocessingPass(resourceManager){
}

PreprocessingPassResult NlExtPurifyPass::apply(AssertionPipeline* assertionsToPreprocess) {
  std::hash_map<Node, Node, NodeHashFunction> cache;
  std::hash_map<Node, Node, NodeHashFunction> bcache;
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

CEGuidedInstPass::CEGuidedInstPass(ResourceManager* resourceManager,
    TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager), 
    d_theoryEngine(theoryEngine){
}

PreprocessingPassResult CEGuidedInstPass::apply(AssertionPipeline* assertionsToPreprocess){
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      d_theoryEngine->getQuantifiersEngine()->getCegInstantiation()->preregisterAssertion( (*assertionsToPreprocess)[i] );
    }
    return PreprocessingPassResult(true);
}

SolveRealAsIntPass::SolveRealAsIntPass(ResourceManager* resourceManager) :
     PreprocessingPass(resourceManager){
}

PreprocessingPassResult SolveRealAsIntPass::apply(AssertionPipeline* assertionsToPreprocess) {
 Chat() << "converting reals to ints..." << std::endl;
 std::hash_map<Node, Node, NodeHashFunction> cache;
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

SolveIntAsBVPass::SolveIntAsBVPass(ResourceManager* resourceManager) :
    PreprocessingPass(resourceManager){
}

PreprocessingPassResult SolveIntAsBVPass::apply(AssertionPipeline* assertionsToPreprocess)
{
  Chat() << "converting ints to bit-vectors..." << std::endl;
  std::hash_map<Node, Node, NodeHashFunction> cache;
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

BitBlastModePass::BitBlastModePass(ResourceManager* resourceManager,
     TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager),
     d_theoryEngine(theoryEngine){
}

PreprocessingPassResult BitBlastModePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_theoryEngine->mkAckermanizationAsssertions(assertionsToPreprocess->ref());
 return PreprocessingPassResult(true);
}

BVAbstractionPass::BVAbstractionPass(ResourceManager* resourceManager,
     SmtEngine* smt, TheoryEngine* theoryEngine) : 
     PreprocessingPass(resourceManager), d_smt(smt), 
     d_theoryEngine(theoryEngine){
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

ConstrainSubtypesPass::ConstrainSubtypesPass(ResourceManager* resourceManager, SmtEngine* smt) : PreprocessingPass(resourceManager), d_smt(smt) {
}

void ConstrainSubtypesPass::constrainSubtypes(TNode top, AssertionPipeline& assertions)
  throw() {
  Trace("constrainSubtypes") << "constrainSubtypes(): looking at " << top << endl;

  set<TNode> done;
  stack<TNode> worklist;
  worklist.push(top);
  done.insert(top);

  do {
    TNode n = worklist.top();
    worklist.pop();

    TypeNode t = n.getType();
    if(t.isPredicateSubtype()) {
      WarningOnce() << "Warning: CVC4 doesn't yet do checking that predicate subtypes are nonempty domains" << endl;
      Node pred = t.getSubtypePredicate();
      Kind k;
      // pred can be a LAMBDA, a function constant, or a datatype tester
      Trace("constrainSubtypes") << "constrainSubtypes(): pred.getType() == " << pred.getType() << endl;
      if(d_smt->d_definedFunctions->find(pred) != d_smt->d_definedFunctions->end()) {
        k = kind::APPLY;
      } else if(pred.getType().isTester()) {
        k = kind::APPLY_TESTER;
      } else {
        k = kind::APPLY_UF;
      }
      Node app = NodeManager::currentNM()->mkNode(k, pred, n);
      Trace("constrainSubtypes") << "constrainSubtypes(): assert(" << k << ") " << app << endl;
      assertions.push_back(app);
    } else if(t.isSubrange()) {
      SubrangeBounds bounds = t.getSubrangeBounds();
      Trace("constrainSubtypes") << "constrainSubtypes(): got bounds " << bounds << endl;
      if(bounds.lower.hasBound()) {
        Node c = NodeManager::currentNM()->mkConst(Rational(bounds.lower.getBound()));
        Node lb = NodeManager::currentNM()->mkNode(kind::LEQ, c, n);
        Trace("constrainSubtypes") << "constrainSubtypes(): assert " << lb << endl;
        assertions.push_back(lb);
      }
      if(bounds.upper.hasBound()) {
        Node c = NodeManager::currentNM()->mkConst(Rational(bounds.upper.getBound()));
        Node ub = NodeManager::currentNM()->mkNode(kind::LEQ, n, c);
        Trace("constrainSubtypes") << "constrainSubtypes(): assert " << ub << endl;
        assertions.push_back(ub);
      }
    }

    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      if(done.find(*i) == done.end()) {
        worklist.push(*i);
        done.insert(*i);
      }
    }
  } while(! worklist.empty());
}

PreprocessingPassResult ConstrainSubtypesPass::apply(AssertionPipeline* assertionsToPreprocess){
    // Any variables of subtype types need to be constrained properly.
    // Careful, here: constrainSubtypes() adds to the back of
    // d_assertions, but we don't need to reprocess those.
    // We also can't use an iterator, because the vector may be moved in
    // memory during this loop.
    Chat() << "constraining subtypes..." << endl;
    for(unsigned i = 0, i_end = assertionsToPreprocess->size(); i != i_end; ++i) {
      constrainSubtypes((*assertionsToPreprocess)[i], *assertionsToPreprocess);
    }
  return PreprocessingPassResult(true);
}

UnconstrainedSimpPass::UnconstrainedSimpPass(ResourceManager* resourceManager,
      TimerStat unconstrainedSimpTime, TheoryEngine* theoryEngine) :
      PreprocessingPass(resourceManager), 
      d_unconstrainedSimpTime(unconstrainedSimpTime), 
      d_theoryEngine(theoryEngine){
}

PreprocessingPassResult UnconstrainedSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
  TimerStat::CodeTimer unconstrainedSimpTimer(d_unconstrainedSimpTime);
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << std::endl;
  d_theoryEngine->ppUnconstrainedSimp(assertionsToPreprocess->ref());
 return PreprocessingPassResult(true);
}

RewritePass::RewritePass(ResourceManager* resourceManager) : 
    PreprocessingPass(resourceManager){
}

PreprocessingPassResult RewritePass::apply(AssertionPipeline* assertionsToPreprocess){
   for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    assertionsToPreprocess->replace(i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
    }
 return PreprocessingPassResult(true);
}

NotUnsatCoresPass::NotUnsatCoresPass(ResourceManager* resourceManager, 
     theory::SubstitutionMap* topLevelSubstitutions) : 
     PreprocessingPass(resourceManager), 
     d_topLevelSubstitutions(topLevelSubstitutions){
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
     
BVToBoolPass::BVToBoolPass(ResourceManager* resourceManager,
      TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager),
      d_theoryEngine(theoryEngine){
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

BoolToBVPass::BoolToBVPass(ResourceManager* resourceManager,
     TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager),
     d_theoryEngine(theoryEngine){
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

SepPreSkolemEmpPass::SepPreSkolemEmpPass(ResourceManager* resourceManager) : PreprocessingPass(resourceManager){
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

QuantifiedPass::QuantifiedPass(ResourceManager* resourceManager, 
   TheoryEngine* theoryEngine, SmtEngine* smt) : 
   PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_smt(smt) { 
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

InferenceOrFairnessPass::InferenceOrFairnessPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_smt(smt){
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

PBRewritePass::PBRewritePass(ResourceManager* resourceManager, theory::arith::PseudoBooleanProcessor* pbsProcessor) : PreprocessingPass(resourceManager), d_pbsProcessor(pbsProcessor){
}

PreprocessingPassResult PBRewritePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_pbsProcessor->learn(assertionsToPreprocess->ref());
    if(d_pbsProcessor->likelyToHelp()){
      d_pbsProcessor->applyReplacements(assertionsToPreprocess->ref());
    }
 return PreprocessingPassResult(true);
}

DoStaticLearningPass::DoStaticLearningPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt, TimerStat staticLearningTime) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_smt(smt), d_staticLearningTime(staticLearningTime){
}

RemoveITEPass::RemoveITEPass(ResourceManager* resourceManager, SmtEngine* smt, IteSkolemMap* iteSkolemMap, RemoveTermFormulas* iteRemover) : PreprocessingPass(resourceManager), d_smt(smt), d_iteSkolemMap(iteSkolemMap), d_iteRemover(iteRemover){
}

PreprocessingPassResult RemoveITEPass::apply(AssertionPipeline* assertionsToPreprocess){
  d_smt->finalOptionsAreSet();
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::removeITEs()" << endl;

  // Remove all of the ITE occurrences and normalize
  d_iteRemover->run(assertionsToPreprocess->ref(), *d_iteSkolemMap, true);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    assertionsToPreprocess->replace(i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
  }
 return PreprocessingPassResult(true);
}

void DoStaticLearningPass::staticLearning(AssertionPipeline* assertionsToPreprocess){
  d_smt->finalOptionsAreSet();
  spendResource(options::preprocessStep());

  TimerStat::CodeTimer staticLearningTimer(d_staticLearningTime);

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

RewriteApplyToConstPass::RewriteApplyToConstPass(ResourceManager* resourceManager, TimerStat rewriteApplyToConstTime) : PreprocessingPass(resourceManager), d_rewriteApplyToConstTime(rewriteApplyToConstTime){
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
    TimerStat::CodeTimer codeTimer(d_rewriteApplyToConstTime);
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      (*assertionsToPreprocess)[i] = theory::Rewriter::rewrite(rewriteApplyToConst((*assertionsToPreprocess)[i]));
    }
 return PreprocessingPassResult(true);
}

TheoryPreprocessPass::TheoryPreprocessPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, TimerStat theoryPreprocessTime) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_theoryPreprocessTime(theoryPreprocessTime){
}

PreprocessingPassResult TheoryPreprocessPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "theory preprocessing..." << endl;
    TimerStat::CodeTimer codeTimer(d_theoryPreprocessTime);
    // Call the theory preprocessors
    d_theoryEngine->preprocessStart();
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      assertionsToPreprocess->replace(i, d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
    }
   return PreprocessingPassResult(true);
}

BitBlastModeEagerPass::BitBlastModeEagerPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine){
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

NoConflictPass::NoConflictPass(ResourceManager* resourceManager, DecisionEngine* decisionEngine, unsigned realAssertionsEnd, IteSkolemMap* iteSkolemMap) : PreprocessingPass(resourceManager), d_decisionEngine(decisionEngine), d_realAssertionsEnd(realAssertionsEnd), d_iteSkolemMap(iteSkolemMap){
}

PreprocessingPassResult NoConflictPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "pushing to decision engine..." << std::endl;
    Assert(iteRewriteAssertionsEnd == assertionsToPreprocess->size());
    d_decisionEngine->addAssertions
      (assertionsToPreprocess->ref(), d_realAssertionsEnd, *d_iteSkolemMap);
 return PreprocessingPassResult(true);
}

CNFPass::CNFPass(ResourceManager* resourceManager, prop::PropEngine* propEngine, TimerStat cnfConversionTime) : PreprocessingPass(resourceManager), d_propEngine(propEngine), d_cnfConversionTime(cnfConversionTime){
}

PreprocessingPassResult CNFPass::apply(AssertionPipeline* assertionsToPreprocess){
   Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_cnfConversionTime);
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      Chat() << "+ " << (*assertionsToPreprocess)[i] << std::endl;
      d_propEngine->assertFormula((*assertionsToPreprocess)[i]);
    }
  return PreprocessingPassResult(true);
}

/**
RepeatSimpPass::RepeatSimpPass(ResourceManager* resourceManager, 
    theory::SubstitutionMap* topLevelSubstitutions,
    unsigned simplifyAssertionsDepth, bool* noConflict, 
    IteSkolemMap iteSkolemMap, unsigned realAssertionsEnd) : 
    PreprocessingPass(resourceManager), 
    d_topLevelSubstitutions(topLevelSubstitutions),
    d_simplifyAssertionsDepth(simplifyAssertionsDepth), 
    noConflict(noConflict), d_iteSkolemMap(iteSkolemMap),
    d_realAssertionsEnd(realAssertionsEnd){
}

bool RepeatSimpPass::checkForBadSkolems(TNode n, TNode skolem, hash_map<Node, bool, NodeHashFunction>& cache)
{
  hash_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = d_iteSkolemMap.find(n);
    bool bad = false;
    if (it != d_iteSkolemMap.end()) {
      if (!((*it).first < n)) {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    if (checkForBadSkolems(n[k], skolem, cache)) {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

void RepeatSimpPass::collectSkolems(TNode n, set<TNode>& skolemSet, hash_map<Node, bool, NodeHashFunction>& cache)
{
  hash_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = d_iteSkolemMap.find(n);
    if (it != d_iteSkolemMap.end()) {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    collectSkolems(n[k], skolemSet, cache);
  }
  cache[n] = true;
}


PreprocessingPassResult RepeatSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "re-simplifying assertions..." << std::endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
  //  *noConflict &= simplifyAssertions();
    if (*noConflict) {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the order in which these variables were introduced
      // during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr mapped to by sk.

      // cache for expression traversal
      std::hash_map<Node, bool, NodeHashFunction> cache;

      // First, find all skolems that appear in the substitution map - their associated iteExpr will need
      // to be moved to the main assertion set
      std::set<TNode> skolemSet;
      theory::SubstitutionMap::iterator pos = d_topLevelSubstitutions->begin();
      for (; pos != d_topLevelSubstitutions->end(); ++pos) {
        collectSkolems((*pos).first, skolemSet, cache);
        collectSkolems((*pos).second, skolemSet, cache);
      }

      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper assertion
      IteSkolemMap::iterator it = d_iteSkolemMap.begin();
      IteSkolemMap::iterator iend = d_iteSkolemMap.end();
      NodeBuilder<> builder(kind::AND);
      builder << (*assertionsToPreprocess)[d_realAssertionsEnd - 1];
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
            bool bad = checkForBadSkolems(iteExpr[0], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[1][1], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[2][1], (*it).first, cache);
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
          d_iteSkolemMap.erase(toErase.back());
          toErase.pop_back();
        }
        (*assertionsToPreprocess)[d_realAssertionsEnd - 1] = theory::Rewriter::rewrite(Node(builder));
       }
      // For some reason this is needed for some benchmarks, such as
      // http://cvc4.cs.nyu.edu/benchmarks/smtlib2/QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      // Figure it out later
      removeITEs();
      //      Assert(iteRewriteAssertionsEnd == d_assertions.size());
    }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-repeat-simplify" << std::endl;
 return PreprocessingPassResult(true);
}

SimplifyAssertionsPass::SimplifyAssertionsPass(
   ResourceManager* resourceManager, unsigned simplifyAssertionsDepth, 
   SmtEngine* smt, bool propagatorNeedsFinish, 
   theory::booleans::CircuitPropagator propagator,
   context::CDO<unsigned> substitutionsIndex,
   std::vector<Node> nonClausalLearnedLiterals, Node dtrue, 
   TimerStat nonclausalSimplificationTime) : 
   PreprocessingPass(resourceManager),
   d_simplifyAssertionsDepth(simplifyAssertionsDepth),
   d_smt(smt), d_propagatorNeedsFinish(propagatorNeedsFinish), 
   d_propagator(propagator), d_substitutionsIndex(substitutionsIndex), 
   d_nonClausalLearnedLiterals(nonClausalLearnedLiterals),
   d_true(dtrue), d_nonclausalSimplificationTime(nonclausalSimplificationTime) {
}

void SimplifyAssertionsPass::addFormula(TNode n, bool inUnsatCore, bool inInput, AssertionPipeline d_assertions)
  throw(TypeCheckingException, LogicException) {

  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << "), inUnsatCore = " << inUnsatCore << ", inInput = " << inInput << endl;

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {

        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
    // rewrite rules are by default in the unsat core because
    // they need to be applied until saturation
    if(options::unsatCores() &&
       n.getKind() == kind::REWRITE_RULE ){
      ProofManager::currentPM()->addUnsatCore(n.toExpr());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n);
  //d_assertions.push_back(Rewriter::rewrite(n));
}

// returns false if it learns a conflict
bool SimplifyAssertionsPass::nonClausalSimplify(AssertionPipeline &d_assertions) {
  spendResource(options::preprocessStep());
  d_smt->finalOptionsAreSet();

  if(options::unsatCores() || options::fewerPreprocessingHoles()) {
    return true;
  }

  TimerStat::CodeTimer nonclausalTimer(d_nonclausalSimplificationTime);

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify()" << endl;
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Trace("simplify") << "Assertion #" << i << " : " << d_assertions[i] << std::endl;
  }

  if(d_propagatorNeedsFinish) {
    d_propagator.finish();
    d_propagatorNeedsFinish = false;
  }
  d_propagator.initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
    // Don't reprocess substitutions
    if (d_substitutionsIndex > 0 && i == d_substitutionsIndex) {
      continue;
    }
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting " << d_assertions[i] << endl;
    Debug("cores") << "d_propagator assertTrue: " << d_assertions[i] << std::endl;
    d_propagator.assertTrue(d_assertions[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (d_propagator.propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    d_assertions.clear();
    addFormula(falseNode, false, false, d_assertions);
    d_propagatorNeedsFinish = true;
    return false;
  }


  Trace("simplify") << "Iterate through " << d_nonClausalLearnedLiterals.size() << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  theory::SubstitutionMap constantPropagations(d_smt->d_context);
  theory::SubstitutionMap newSubstitutions(d_smt->d_context);
  theory::SubstitutionMap::iterator pos;
  unsigned j = 0;
  for(unsigned i = 0, i_end = d_nonClausalLearnedLiterals.size(); i < i_end; ++ i) {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = d_nonClausalLearnedLiterals[i];
    Assert(theory::Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(d_topLevelSubstitutions.apply(learnedLiteral) == learnedLiteral);
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
      ++d_smt->d_stats->d_numConstantProps;
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
                          << d_nonClausalLearnedLiterals[i] << endl;
        Assert(!options::unsatCores());
        d_assertions.clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false, d_assertions);
        d_propagatorNeedsFinish = true;
        return false;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "solving " << learnedLiteral << endl;

    Theory::PPAssertStatus solveStatus =
      d_smt->d_theoryEngine->solve(learnedLiteral, newSubstitutions);

    switch (solveStatus) {
      case Theory::PP_ASSERT_STATUS_SOLVED: {
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
      case Theory::PP_ASSERT_STATUS_CONFLICT:
        // If in conflict, we return false
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict while solving "
                          << learnedLiteral << endl;
        Assert(!options::unsatCores());
        d_assertions.clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false, d_assertions);
        d_propagatorNeedsFinish = true;
        return false;
      default:
        if (d_doConstantProp && learnedLiteral.getKind() == kind::EQUAL && (learnedLiteral[0].isConst() || learnedLiteral[1].isConst())) {
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
          Assert(d_topLevelSubstitutions.apply(t) == t);
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
          d_nonClausalLearnedLiterals[j++] = d_nonClausalLearnedLiterals[i];
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
    Assert(d_topLevelSubstitutions.apply((*pos).first) == (*pos).first);
    Assert(d_topLevelSubstitutions.apply((*pos).second) == (*pos).second);
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
//#endif  CVC4_ASSERTIONS 

  // Resize the learnt
  Trace("simplify") << "Resize non-clausal learned literals to " << j << std::endl;
  d_nonClausalLearnedLiterals.resize(j);

  hash_set<TNode, TNodeHashFunction> s;
  Trace("debugging") << "NonClausal simplify pre-preprocess\n";
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Node assertion = d_assertions[i];
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
      ++d_smt->d_stats->d_numConstantProps;
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
      assertion = theory::Rewriter::rewrite(assertionNew);
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
    }
    Trace("debugging") << "\n";
    s.insert(assertion);
    d_assertions.replace(i, assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: "
                      << assertion << endl;
  }

  // If in incremental mode, add substitutions to the list of assertions
  if (d_substitutionsIndex > 0) {
    NodeBuilder<> substitutionsBuilder(kind::AND);
    substitutionsBuilder << d_assertions[d_substitutionsIndex];
    pos = newSubstitutions.begin();
    for (; pos != newSubstitutions.end(); ++pos) {
      // Add back this substitution as an assertion
      TNode lhs = (*pos).first, rhs = newSubstitutions.apply((*pos).second);
      Node n = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
      substitutionsBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will notify SAT layer of substitution: " << n << endl;
    }
    if (substitutionsBuilder.getNumChildren() > 1) {
      d_assertions.replace(d_substitutionsIndex,
        theory::Rewriter::rewrite(Node(substitutionsBuilder)));
    }
  } else {
    // If not in incremental mode, must add substitutions to model
    TheoryModel* m = d_smt->d_theoryEngine->getModel();
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
  Assert(d_realAssertionsEnd <= d_assertions.size());
  learnedBuilder << d_assertions[d_realAssertionsEnd - 1];

  for (unsigned i = 0; i < d_nonClausalLearnedLiterals.size(); ++ i) {
    Node learned = d_nonClausalLearnedLiterals[i];
    Assert(d_topLevelSubstitutions.apply(learned) == learned);
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
      ++d_smt->d_stats->d_numConstantProps;
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
  d_nonClausalLearnedLiterals.clear();

  for (pos = constantPropagations.begin(); pos != constantPropagations.end(); ++pos) {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(d_topLevelSubstitutions.apply(cProp) == cProp);
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
  d_topLevelSubstitutions.addSubstitutions(newSubstitutions);

  if(learnedBuilder.getNumChildren() > 1) {
    d_assertions.replace(d_realAssertionsEnd - 1,
      theory::Rewriter::rewrite(Node(learnedBuilder)));
  }

  d_propagatorNeedsFinish = true;
  return true;
}

// returns false if simplification led to "false"
PreprocessingPassResult SimplifyAssertionsPass::apply(AssertionPipeline* assertionsToPreprocess)
  throw(TypeCheckingException, LogicException, UnsafeInterruptException) {
  spendResource(options::preprocessStep());
  Assert(d_smt->d_pendingPops == 0);
  try {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    dumpAssertions("pre-nonclausal", *assertionsToPreprocess);

    if(options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      // Perform non-clausal simplification
      Chat() << "...performing nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << "performing non-clausal simplification" << endl;
      bool noConflict = nonClausalSimplify(*assertionsToPreprocess);
      if(!noConflict) {
        return false;
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if( // check that option is on
          options::arithMLTrick() &&
          // miplib rewrites aren't safe in incremental mode
          ! options::incrementalSolving() &&
          // only useful in arith
          d_smt->d_logic.isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          d_realAssertionsEnd == assertionsToPreprocess->size() ) {
        Chat() << "...fixing miplib encodings..." << endl;
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "looking for miplib pseudobooleans..." << endl;

        TimerStat::CodeTimer miplibTimer(d_smt->d_stats->d_miplibPassTime);

        doMiplibTrick();
      } else {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass (either incrementalSolving is on, or miplib pbs are turned off)..." << endl;
      }
    }

    dumpAssertions("post-nonclausal", *assertionsToPreprocess);
    Trace("smt") << "POST nonClausalSimplify" << endl;
    Debug("smt") << " d_assertions     : " << assertionsToPreprocess->size() << endl;

    // before ppRewrite check if only core theory for BV theory
    d_smt->d_theoryEngine->staticInitializeBVOptions(assertionsToPreprocess->ref());

    dumpAssertions("pre-theorypp", *assertionsToPreprocess);

    // Theory preprocessing
    if (d_smt->d_earlyTheoryPP) {
      Chat() << "...doing early theory preprocessing..." << endl;
      TimerStat::CodeTimer codeTimer(d_smt->d_stats->d_theoryPreprocessTime);
      // Call the theory preprocessors
      d_smt->d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
        Assert(theory::Rewriter::rewrite((*assertionsToPreprocess)[i]) == (*assertionsTopreprocess)[i]);
        assertionsToPreprocess->replace(i, d_smt->d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
        Assert(theory::Rewriter::rewrite((*assertionsToPreprocess)[i]) == (*assertionsToPreprocess)[i]);
      }
    }

    dumpAssertions("post-theorypp", *assertionsToPreprocess);
    Trace("smt") << "POST theoryPP" << endl;
    Debug("smt") << " d_assertions     : " << assertionsToPreprocess->size() << endl;

    // ITE simplification
    if(options::doITESimp() &&
       (d_simplifyAssertionsDepth <= 1 || options::doITESimpOnRepeat())) {
      Chat() << "...doing ITE simplification..." << endl;
      bool noConflict = simpITE();
      if(!noConflict){
        Chat() << "...ITE simplification found unsat..." << endl;
        return false;
      }
    }

    dumpAssertions("post-itesimp", *assertionsToPreprocess);
    Trace("smt") << "POST iteSimp" << endl;
    Debug("smt") << " d_assertions     : " << assertionsToPreprocess->size() << endl;

    // Unconstrained simplification
    if(options::unconstrainedSimp()) {
      Chat() << "...doing unconstrained simplification..." << endl;
      preproc::UnconstrainedSimpPass pass(d_resourceManager, d_smt->d_stats->d_unconstrainedSimpTime, d_smt->d_theoryEngine);
      pass.apply(assertionsToPreprocess);
   }

    dumpAssertions("post-unconstrained", *assertionsToPreprocess);
    Trace("smt") << "POST unconstrainedSimp" << endl;
    Debug("smt") << " d_assertions     : " << assertionsToPreprocess->size() << endl;

    if(options::repeatSimp() && options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      Chat() << "...doing another round of nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << " doing repeated simplification" << endl;
      bool noConflict = nonClausalSimplify(*assertionsToPreprocess);
      if(!noConflict) {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", *assertionsToPreprocess);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " d_assertions     : " << assertionsToPreprocess->size() << endl;

  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
  return PreprocessingPassResult(true); 
}
**/

}  // namespace preproc
}  // namespace CVC4
