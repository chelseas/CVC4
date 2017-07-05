#include "preproc/preprocessing_passes_core.h"

#include <unordered_map>
#include <string>
#include "theory/quantifiers/quant_util.h"
#include "options/smt_options.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preproc {

NlExtPurifyPass::NlExtPurifyPass(ResourceManager* resourceManager) : PreprocessingPass(resourceManager){
}

void NlExtPurifyPass::apply(std::vector<Node>* assertionsToPreprocess) {
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::unordered_map<Node, Node, NodeHashFunction> bcache;
  std::vector<Node> var_eq;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    (*assertionsToPreprocess)[i] =
        purifyNlTerms((*assertionsToPreprocess)[i], cache, bcache, var_eq);
  }
  if (!var_eq.empty()) {
    unsigned lastIndex = assertionsToPreprocess->size() - 1;
    var_eq.insert(var_eq.begin(), (*assertionsToPreprocess)[lastIndex]);
    (*assertionsToPreprocess)[lastIndex] =
        NodeManager::currentNM()->mkNode(kind::AND, var_eq);
  }
}

Node NlExtPurifyPass::purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                                    std::vector<Node>& var_eq,
                                    bool beneathMult) {
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

SolveRealAsIntPass::SolveRealAsIntPass(ResourceManager* resourceManager) : PreprocessingPass(resourceManager){
}

void SolveRealAsIntPass::apply(std::vector<Node>* assertionsToPreprocess) {
 Chat() << "converting reals to ints..." << std::endl;
 std::unordered_map<Node, Node, NodeHashFunction> cache;
 std::vector<Node> var_eq;
 for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
 (*assertionsToPreprocess)[i] = 
  realToInt((*assertionsToPreprocess)[i], cache, var_eq);
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

SolveIntAsBVPass::SolveIntAsBVPass(ResourceManager* resourceManager) : PreprocessingPass(resourceManager){
}

void SolveIntAsBVPass::apply(std::vector<Node>* assertionsToPreprocess)
{
  Chat() << "converting ints to bit-vectors..." << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for(unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
  (*assertionsToPreprocess)[i] =
    intToBV((*assertionsToPreprocess)[i], cache);
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

void BVToBoolPass::apply(std::vector<Node>* assertionsToPreprocess){
  dumpAssertions("pre-bv-to-bool", *assertionsToPreprocess);
  Chat() << "...doing bvToBool..." << std::endl;
  bvToBool(assertionsToPreprocess);
  dumpAssertions("post-bv-to-bool", *assertionsToPreprocess);
  Trace("smt") << "POST bvToBool" << std::endl;
}

BVToBoolPass::BVToBoolPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager) , d_theoryEngine(theoryEngine){
}

void BVToBoolPass::bvToBool(std::vector<Node>* assertionsToPreprocess) {
  Trace("bv-to-bool") << "SmtEnginePrivate::bvToBool()" << std::endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBvToBool((*assertionsToPreprocess), new_assertions);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    (*assertionsToPreprocess)[i] =
      theory::Rewriter::rewrite(new_assertions[i]);
  }
}

BoolToBVPass::BoolToBVPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine) : PreprocessingPass(resourceManager) , d_theoryEngine(theoryEngine){
}
  
void BoolToBVPass::boolToBv(std::vector<Node>* assertionsToPreprocess) {
  Trace("bool-to-bv") << "SmtEnginePrivate::boolToBv()" << std::endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBoolToBv((*assertionsToPreprocess), new_assertions);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++ i) {
    (*assertionsToPreprocess)[i] = 
      theory::Rewriter::rewrite(new_assertions[i]);
   }
}

void BoolToBVPass::apply(std::vector<Node>* assertionsToPreprocess){
    dumpAssertions("pre-bool-to-bv", *assertionsToPreprocess);
    Chat() << "...doing boolToBv..." << std::endl;
    boolToBv(assertionsToPreprocess);
    dumpAssertions("post-bool-to-bv", *assertionsToPreprocess);
    Trace("smt") << "POST boolToBv" << std::endl;
}

}  // namespace preproc
}  // namespace CVC4
