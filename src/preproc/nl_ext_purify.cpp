/*********************                                                        */
/*! \file nl_ext_purify.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for nl ext pass
 **
 ** Preprocessing pass for nl ext pass.
 **/
#include "preproc/nl_ext_purify.h"
#include <string>

namespace CVC4 {
namespace preproc {

NlExtPurifyPass::NlExtPurifyPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "nlExtPurify", true) {}

PreprocessingPassResult NlExtPurifyPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::unordered_map<Node, Node, NodeHashFunction> bcache;
  std::vector<Node> var_eq;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(
        i, purifyNlTerms((*assertionsToPreprocess)[i], cache, bcache, var_eq));
  }
  if (!var_eq.empty()) {
    unsigned lastIndex = assertionsToPreprocess->size() - 1;
    var_eq.insert(var_eq.begin(), (*assertionsToPreprocess)[lastIndex]);
    assertionsToPreprocess->replace(
        lastIndex, NodeManager::currentNM()->mkNode(kind::AND, var_eq));
  }
  return NO_CONFLICT;
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

}  // namespace preproc
}  // namespace CVC4
