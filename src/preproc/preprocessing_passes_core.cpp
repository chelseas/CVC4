#include "preproc/preprocessing_passes_core.h"

#include <unordered_map>
#include <string>
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

namespace CVC4 {
namespace preproc {

NlExtPurifyPass::NlExtPurifyPass(ResourceManager* resourceManager) :
    PreprocessingPass(resourceManager){
}

void NlExtPurifyPass::apply(smt::AssertionPipeline* assertionsToPreprocess) {
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

void CEGuidedInstPass::apply(AssertionPipeline* assertionsToPreprocess){
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      d_theoryEngine->getQuantifiersEngine()->getCegInstantiation()->preregisterAssertion( (*assertionsToPreprocess)[i] );
    }
}

SolveRealAsIntPass::SolveRealAsIntPass(ResourceManager* resourceManager) :
     PreprocessingPass(resourceManager){
}

void SolveRealAsIntPass::apply(AssertionPipeline* assertionsToPreprocess) {
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

void SolveIntAsBVPass::apply(AssertionPipeline* assertionsToPreprocess)
{
  Chat() << "converting ints to bit-vectors..." << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
  assertionsToPreprocess->replace(i, intToBV((*assertionsToPreprocess)[i], cache) );
  }
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

void BitBlastModePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_theoryEngine->mkAckermanizationAsssertions(assertionsToPreprocess->ref());
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
 
void BVAbstractionPass::apply(AssertionPipeline* assertionsToPreprocess){
    dumpAssertions("pre-bv-abstraction", *assertionsToPreprocess);
    bvAbstraction(assertionsToPreprocess);
    dumpAssertions("post-bv-abstraction", *assertionsToPreprocess);
} 

UnconstrainedSimpPass::UnconstrainedSimpPass(ResourceManager* resourceManager,
      TimerStat unconstrainedSimpTime, TheoryEngine* theoryEngine) :
      PreprocessingPass(resourceManager), 
      d_unconstrainedSimpTime(unconstrainedSimpTime), 
      d_theoryEngine(theoryEngine){
}

void UnconstrainedSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
  TimerStat::CodeTimer unconstrainedSimpTimer(d_unconstrainedSimpTime);
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << std::endl;
  d_theoryEngine->ppUnconstrainedSimp(assertionsToPreprocess->ref());
}

RewritePass::RewritePass(ResourceManager* resourceManager) : 
    PreprocessingPass(resourceManager){
}

void RewritePass::apply(AssertionPipeline* assertionsToPreprocess){
   for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    assertionsToPreprocess->replace(i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
    }
}

NotUnsatCoresPass::NotUnsatCoresPass(ResourceManager* resourceManager, 
     theory::SubstitutionMap* topLevelSubstitutions) : 
     PreprocessingPass(resourceManager), 
     d_topLevelSubstitutions(topLevelSubstitutions){
}

void NotUnsatCoresPass::apply(AssertionPipeline* assertionsToPreprocess){
  Chat() << "applying substitutions..." << std::endl;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                        << "applying substitutions" << std::endl;
      for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
        Trace("simplify") << "applying to " << (*assertionsToPreprocess)[i] << std::endl;
        spendResource(options::preprocessStep());
        assertionsToPreprocess->replace(i, theory::Rewriter::rewrite(d_topLevelSubstitutions->apply((*assertionsToPreprocess)[i])));
        Trace("simplify") << "  got " << (*assertionsToPreprocess)[i] << std::endl;
       }
}
     
BVToBoolPass::BVToBoolPass(ResourceManager* resourceManager,
      TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager),
      d_theoryEngine(theoryEngine){
}

void BVToBoolPass::apply(AssertionPipeline* assertionsToPreprocess){
  dumpAssertions("pre-bv-to-bool", *assertionsToPreprocess);
  Chat() << "...doing bvToBool..." << std::endl;
  bvToBool(assertionsToPreprocess);
  //A rewrite pass was formerly here that has been moved to after the dump
  dumpAssertions("post-bv-to-bool", *assertionsToPreprocess);
  Trace("smt") << "POST bvToBool" << std::endl;
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

void BoolToBVPass::apply(AssertionPipeline* assertionsToPreprocess){
    dumpAssertions("pre-bool-to-bv", *assertionsToPreprocess);
    Chat() << "...doing boolToBv..." << std::endl;
    boolToBv(assertionsToPreprocess);
    dumpAssertions("post-bool-to-bv", *assertionsToPreprocess);
    Trace("smt") << "POST boolToBv" << std::endl;
}

SepPreSkolemEmpPass::SepPreSkolemEmpPass(ResourceManager* resourceManager) : PreprocessingPass(resourceManager){
}

void SepPreSkolemEmpPass::apply(AssertionPipeline* assertionsToPreprocess){
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = theory::sep::TheorySepRewriter::preprocess( prev );
      if( next!=prev ){
        assertionsToPreprocess->replace(i, theory::Rewriter::rewrite( next ));
        Trace("sep-preprocess") << "*** Preprocess sep " << prev << std::endl;
        Trace("sep-preprocess") << "   ...got " << (*assertionsToPreprocess)[i] << std::endl;
       }
  }
}

QuantifiedPass::QuantifiedPass(ResourceManager* resourceManager, 
   TheoryEngine* theoryEngine, NodeList* &fmfRecFunctionsDefined, 
   std::map<Node,TypeNode> &fmfRecFunctionsAbs, 
   std::map<Node, std::vector<Node> > &fmfRecFunctionsConcrete) : 
   PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), 
   d_fmfRecFunctionsDefined(fmfRecFunctionsDefined), 
   d_fmfRecFunctionsAbs(fmfRecFunctionsAbs), 
   d_fmfRecFunctionsConcrete(fmfRecFunctionsConcrete){
}

void QuantifiedPass::apply(AssertionPipeline* assertionsToPreprocess){
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
      Assert( d_fmfRecFunctionsDefined!=NULL );
      //must carry over current definitions (for incremental)
      for( context::CDList<Node>::const_iterator fit = d_fmfRecFunctionsDefined->begin();
           fit != d_fmfRecFunctionsDefined->end(); ++fit ) {
        Node f = (*fit);
        Assert( d_fmfRecFunctionsAbs.find( f )!= d_fmfRecFunctionsAbs.end() );
        TypeNode ft = d_fmfRecFunctionsAbs[f];
        fdf.d_sorts[f] = ft;
        std::map< Node, std::vector< Node > >::iterator fcit = d_fmfRecFunctionsConcrete.find( f );
        Assert( fcit!= d_fmfRecFunctionsConcrete.end() );
        for( unsigned j=0; j<fcit->second.size(); j++ ){
          fdf.d_input_arg_inj[f].push_back( fcit->second[j] );
        }
      }
      fdf.simplify(assertionsToPreprocess->ref());
      //must store new definitions (for incremental)
      for( unsigned i=0; i<fdf.d_funcs.size(); i++ ){
        Node f = fdf.d_funcs[i];
        d_fmfRecFunctionsAbs[f] = fdf.d_sorts[f];
        d_fmfRecFunctionsConcrete[f].clear();
        for( unsigned j=0; j<fdf.d_input_arg_inj[f].size(); j++ ){
          d_fmfRecFunctionsConcrete[f].push_back( fdf.d_input_arg_inj[f][j] );
        }
        d_fmfRecFunctionsDefined->push_back( f );
      }
    }
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-quant-preprocess" << std::endl;
}

InferenceOrFairnessPass::InferenceOrFairnessPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_smt(smt){
}

void InferenceOrFairnessPass::apply(AssertionPipeline* assertionsToPreprocess){
     //sort inference technique
    SortInference * si = d_theoryEngine->getSortInference();
    si->simplify( assertionsToPreprocess->ref(), options::sortInference(), options::ufssFairnessMonotone() );
    for( std::map< Node, Node >::iterator it = si->d_model_replace_f.begin(); it != si->d_model_replace_f.end(); ++it ){
      d_smt->setPrintFuncInModel( it->first.toExpr(), false );
      d_smt->setPrintFuncInModel( it->second.toExpr(), true );
    }
}

PBRewritePass::PBRewritePass(ResourceManager* resourceManager, theory::arith::PseudoBooleanProcessor* pbsProcessor) : PreprocessingPass(resourceManager), d_pbsProcessor(pbsProcessor){
}

void PBRewritePass::apply(AssertionPipeline* assertionsToPreprocess){
  d_pbsProcessor->learn(assertionsToPreprocess->ref());
    if(d_pbsProcessor->likelyToHelp()){
      d_pbsProcessor->applyReplacements(assertionsToPreprocess->ref());
    }
}

DoStaticLearningPass::DoStaticLearningPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt, TimerStat staticLearningTime) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine), d_smt(smt), d_staticLearningTime(staticLearningTime){
}

void DoStaticLearningPass::staticLearning(AssertionPipeline* assertionsToPreprocess){
/*  d_smt->finalOptionsAreSet();
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
  }*/
}

void DoStaticLearningPass::apply(AssertionPipeline* assertionsToPreprocess){
  /*  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-static-learning" << std::endl;
    // Perform static learning
    Chat() << "doing static learning..." << std::endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): "
                      << "performing static learning" << std::endl;
    staticLearning(assertionsToPreprocess);
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-static-learning" << std::endl;*/
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

void RewriteApplyToConstPass::apply(AssertionPipeline* assertionsToPreprocess){
   Chat() << "Rewriting applies to constants..." << std::endl;
    TimerStat::CodeTimer codeTimer(d_rewriteApplyToConstTime);
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
      (*assertionsToPreprocess)[i] = theory::Rewriter::rewrite(rewriteApplyToConst((*assertionsToPreprocess)[i]));
    }
}

BitBlastModeEagerPass::BitBlastModeEagerPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager), d_theoryEngine(theoryEngine){
}

void BitBlastModeEagerPass::apply(AssertionPipeline* assertionsToPreprocess){
    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
      TNode atom = (*assertionsToPreprocess)[i];
      Node eager_atom = NodeManager::currentNM()->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
      assertionsToPreprocess->replace(i, eager_atom);
      theory::TheoryModel* m = d_theoryEngine->getModel();
      m->addSubstitution(eager_atom, atom);
    }
}

NoConflictPass::NoConflictPass(ResourceManager* resourceManager, DecisionEngine* decisionEngine, unsigned realAssertionsEnd, IteSkolemMap* iteSkolemMap) : PreprocessingPass(resourceManager), d_decisionEngine(decisionEngine), d_realAssertionsEnd(realAssertionsEnd), d_iteSkolemMap(iteSkolemMap){
}

void NoConflictPass::apply(AssertionPipeline* assertionsToPreprocess){
    Chat() << "pushing to decision engine..." << std::endl;
    Assert(iteRewriteAssertionsEnd == assertionsToPreprocess->size());
    d_decisionEngine->addAssertions
      (assertionsToPreprocess->ref(), d_realAssertionsEnd, *d_iteSkolemMap);
}

RepeatSimpPass::RepeatSimpPass(ResourceManager* resourceManager, theory::SubstitutionMap* topLevelSubstitutions, unsigned simplifyAssertionsDepth, bool* noConflict) : PreprocessingPass(resourceManager), d_topLevelSubstitutions(topLevelSubstitutions), d_simplifyAssertionsDepth(simplifyAssertionsDepth), noConflict(noConflict){
}

// returns false if simplification led to "false"
bool RepeatSimpPass::simplifyAssertions(){
/*  throw(TypeCheckingException, LogicException, UnsafeInterruptException) {
  spendResource(options::preprocessStep());
  Assert(d_smt.d_pendingPops == 0);
  try {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    dumpAssertions("pre-nonclausal", d_assertions);

    if(options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      // Perform non-clausal simplification
      Chat() << "...performing nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << "performing non-clausal simplification" << endl;
      bool noConflict = nonClausalSimplify();
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
          d_smt.d_logic.isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          d_realAssertionsEnd == d_assertions.size() ) {
        Chat() << "...fixing miplib encodings..." << endl;
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "looking for miplib pseudobooleans..." << endl;

        TimerStat::CodeTimer miplibTimer(d_smt.d_stats->d_miplibPassTime);

        doMiplibTrick();
      } else {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass (either incrementalSolving is on, or miplib pbs are turned off)..." << endl;
      }
    }

    dumpAssertions("post-nonclausal", d_assertions);
    Trace("smt") << "POST nonClausalSimplify" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // before ppRewrite check if only core theory for BV theory
    d_smt.d_theoryEngine->staticInitializeBVOptions(d_assertions.ref());

    dumpAssertions("pre-theorypp", d_assertions);

    // Theory preprocessing
    if (d_smt.d_earlyTheoryPP) {
      Chat() << "...doing early theory preprocessing..." << endl;
      TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
      // Call the theory preprocessors
      d_smt.d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < d_assertions.size(); ++ i) {
        Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
        d_assertions.replace(i, d_smt.d_theoryEngine->preprocess(d_assertions[i]));
        Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
      }
    }

    dumpAssertions("post-theorypp", d_assertions);
    Trace("smt") << "POST theoryPP" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

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

    dumpAssertions("post-itesimp", d_assertions);
    Trace("smt") << "POST iteSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // Unconstrained simplification
    if(options::unconstrainedSimp()) {
      Chat() << "...doing unconstrained simplification..." << endl;
      preproc::UnconstrainedSimpPass pass(d_resourceManager, d_smt.d_stats->d_unconstrainedSimpTime, d_smt.d_theoryEngine);
      pass.apply(&d_assertions);
   }

    dumpAssertions("post-unconstrained", d_assertions);
    Trace("smt") << "POST unconstrainedSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    if(options::repeatSimp() && options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      Chat() << "...doing another round of nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << " doing repeated simplification" << endl;
      bool noConflict = nonClausalSimplify();
      if(!noConflict) {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", d_assertions);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

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
  return true;*/
  return true;
}

void RepeatSimpPass::apply(AssertionPipeline* assertionsToPreprocess){
/*   Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-repeat-simplify" << std::endl;
    Chat() << "re-simplifying assertions..." << std::endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    *noConflict &= simplifyAssertions();
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
      builder << d_assertions[d_realAssertionsEnd - 1];
      std::vector<TNode> toErase;
      for (; it != iend; ++it) {
        if (skolemSet.find((*it).first) == skolemSet.end()) {
          TNode iteExpr = d_assertions[(*it).second];
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
        d_assertions[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
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
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-repeat-simplify" << std::endl;*/
}

}  // namespace preproc
}  // namespace CVC4
