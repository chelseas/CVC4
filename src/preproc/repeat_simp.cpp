/*********************                                                        */
/*! \file repeat_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that repeats simp
 **
 ** Preprocessing pass that repeats simp.
 **/
#include "preproc/repeat_simp.h"

namespace CVC4 {
namespace preproc {

RepeatSimpPass::RepeatSimpPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "repeatSimp", true) {}

/**
 * Helper function to fix up assertion list to restore invariants needed after
 * ite removal.
 */
bool RepeatSimpPass::checkForBadSkolems(
    TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache,
    AssertionPipeline* assertionsToPreprocess) {
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

/**
 * Helper function to fix up assertion list to restore invariants needed after
 * ite removal.
 */
void RepeatSimpPass::collectSkolems(
    TNode n, set<TNode>& skolemSet,
    unordered_map<Node, bool, NodeHashFunction>& cache,
    AssertionPipeline* assertionsToPreprocess) {
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

PreprocessingPassResult RepeatSimpPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  // Need to fix up assertion list to maintain invariants:
  // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the
  // order in which these variables were introduced
  // during ite removal.
  // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr
  // mapped to by sk.

  // cache for expression traversal
  std::unordered_map<Node, bool, NodeHashFunction> cache;

  // First, find all skolems that appear in the substitution map - their
  // associated iteExpr will need
  // to be moved to the main assertion set
  std::set<TNode> skolemSet;
  theory::SubstitutionMap::iterator pos =
      assertionsToPreprocess->getTopLevelSubstitutions()->begin();
  for (; pos != assertionsToPreprocess->getTopLevelSubstitutions()->end();
       ++pos) {
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
  builder << (*assertionsToPreprocess)
          [assertionsToPreprocess->getRealAssertionsEnd() - 1];
  std::vector<TNode> toErase;
  for (; it != iend; ++it) {
    if (skolemSet.find((*it).first) == skolemSet.end()) {
      TNode iteExpr = (*assertionsToPreprocess)[(*it).second];
      if (iteExpr.getKind() == kind::ITE &&
          iteExpr[1].getKind() == kind::EQUAL && iteExpr[1][0] == (*it).first &&
          iteExpr[2].getKind() == kind::EQUAL && iteExpr[2][0] == (*it).first) {
        cache.clear();
        bool bad = checkForBadSkolems(iteExpr[0], (*it).first, cache,
                                      assertionsToPreprocess);
        bad = bad || checkForBadSkolems(iteExpr[1][1], (*it).first, cache,
                                        assertionsToPreprocess);
        bad = bad || checkForBadSkolems(iteExpr[2][1], (*it).first, cache,
                                        assertionsToPreprocess);
        if (!bad) {
          continue;
        }
      }
    }
    // Move this iteExpr into the main assertions
    builder << (*assertionsToPreprocess)[(*it).second];
    (*assertionsToPreprocess)[(*it).second] =
        NodeManager::currentNM()->mkConst<bool>(true);
    toErase.push_back((*it).first);
  }
  if (builder.getNumChildren() > 1) {
    while (!toErase.empty()) {
      assertionsToPreprocess->getSkolemMap()->erase(toErase.back());
      toErase.pop_back();
    }
    (*assertionsToPreprocess)[assertionsToPreprocess->getRealAssertionsEnd() -
                              1] = theory::Rewriter::rewrite(Node(builder));
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
