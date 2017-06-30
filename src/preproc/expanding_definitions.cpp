/*********************                                                        */
/*! \file expanding_definitions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for expanding definitions
 **
 ** preprocessing pass for expanding definitions
 **/
#include "preproc/expanding_definitions.h"
#include <stack>
#include <string>
#include "expr/node_manager_attributes.h"
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "util/ntuple.h"

namespace CVC4 {
namespace preproc {

ExpandingDefinitionsPass::ExpandingDefinitionsPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "expandingDefinitions", true) {}

Node ExpandingDefinitionsPass::expandDefinitions(
    TNode n, unordered_map<Node, Node, NodeHashFunction>& cache,
    bool expandOnly) throw(TypeCheckingException, LogicException,
                           UnsafeInterruptException) {
  stack<triple<Node, Node, bool> > worklist;
  stack<Node> result;
  worklist.push(make_triple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the
  // output / rewritten node
  // and finally a flag tracking whether the children have been explored (i.e.
  // if this is a downward
  // or upward pass).

  do {
    spendResource(options::preprocessStep());
    n = worklist.top().first;           // n is the input / original
    Node node = worklist.top().second;  // node is the output / result
    bool childrenPushed = worklist.top().third;
    worklist.pop();

    // Working downwards
    if (!childrenPushed) {
      Kind k = n.getKind();

      // Apart from apply, we can short circuit leaves
      if (k != kind::APPLY && n.getNumChildren() == 0) {
        if (d_api->isDefinedFunction(n)) {
          // replacement must be closed
          DefinedFunction def = (d_api->getDefinedFunction(n));
          if (def.getFormals().size() > 0) {
            result.push(NodeManager::currentNM()->mkNode(
                kind::LAMBDA, NodeManager::currentNM()->mkNode(
                                  kind::BOUND_VAR_LIST, def.getFormals()),
                def.getFormula()));
            continue;
          }
          // don't bother putting in the cache
          result.push(def.getFormula());
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit =
          cache.find(n);
      if (cacheHit != cache.end()) {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it
      bool doExpand = k == kind::APPLY;
      if (!doExpand) {
        if (options::macrosQuant()) {
          // expand if we have inferred an operator corresponds to a defined
          // function
          doExpand = k == kind::APPLY_UF &&
                     d_api->isDefinedFunction(n.getOperator().toExpr());
        }
      }
      if (doExpand) {
        vector<Node> formals;
        TNode fm;
        if (n.getOperator().getKind() == kind::LAMBDA) {
          TNode op = n.getOperator();
          // lambda
          for (unsigned i = 0; i < op[0].getNumChildren(); i++) {
            formals.push_back(op[0][i]);
          }
          fm = op[1];
        } else {
          // application of a user-defined symbol
          TNode func = n.getOperator();
          if (!d_api->isDefinedFunction(func)) {
            throw TypeCheckingException(
                n.toExpr(),
                string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (d_api->getDefinedFunction(func));
          formals = def.getFormals();

          if (Debug.isOn("expand")) {
            Debug("expand") << "found: " << n << endl;
            Debug("expand") << " func: " << func << endl;
            string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << endl;
          }
          if (Debug.isOn("expand")) {
            Debug("expand") << " defn: " << def.getFunction() << endl
                            << "       [";
            if (formals.size() > 0) {
              copy(formals.begin(), formals.end() - 1,
                   ostream_iterator<Node>(Debug("expand"), ", "));
              Debug("expand") << formals.back();
            }
            Debug("expand") << "]" << endl
                            << "       " << def.getFunction().getType() << endl
                            << "       " << def.getFormula() << endl;
          }

          fm = def.getFormula();
        }

        Node instance =
            fm.substitute(formals.begin(), formals.end(), n.begin(), n.end());
        Debug("expand") << "made : " << instance << endl;

        Node expanded = expandDefinitions(instance, cache, expandOnly);
        cache[n] = (n == expanded ? Node::null() : expanded);
        result.push(expanded);
        continue;

      } else if (!expandOnly) {
        // do not do any theory stuff if expandOnly is true
        Assert(d_smt != NULL);
        theory::Theory* t = d_theoryEngine->theoryOf(node);

        Assert(t != NULL);
        LogicRequest req(*d_smt);
        node = t->expandDefinition(req, n);
      }

      // there should be children here, otherwise we short-circuited a
      // result-push/continue, above
      if (node.getNumChildren() == 0) {
        Debug("expand") << "Unexpectedly no children..." << node << endl;
      }
      // This invariant holds at the moment but it is concievable that a new
      // theory
      // might introduce a kind which can have children before definition
      // expansion but doesn't
      // afterwards.  If this happens, remove this assertion.
      Assert(node.getNumChildren() > 0);

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(
          make_triple(Node(n), node, true));  // Original and rewritten result

      for (size_t i = 0; i < node.getNumChildren(); ++i) {
        worklist.push(
            make_triple(node[i], node[i],
                        false));  // Rewrite the children of the result only
      }

    } else {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << endl;
      // cout << "cons : " << node << endl;
      NodeBuilder<> nb(node.getKind());
      if (node.getMetaKind() == kind::metakind::PARAMETERIZED) {
        Debug("expand") << "op   : " << node.getOperator() << endl;
        // cout << "op   : " << node.getOperator() << endl;
        nb << node.getOperator();
      }
      for (size_t i = 0; i < node.getNumChildren(); ++i) {
        Assert(!result.empty());
        Node expanded = result.top();
        result.pop();
        // cout << "exchld : " << expanded << endl;
        Debug("expand") << "exchld : " << expanded << endl;
        nb << expanded;
      }
      node = nb;
      cache[n] = n == node ? Node::null()
                           : node;  // Only cache once all subterms are expanded
      result.push(node);
    }
  } while (!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

PreprocessingPassResult ExpandingDefinitionsPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_theoryEngine = d_api->getTheoryEngine();
  unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(
        i, expandDefinitions((*assertionsToPreprocess)[i], cache));
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
