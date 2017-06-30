/*********************                                                        */
/*! \file simp_ite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for simplifying ITEs
 ** Preprocessing pass for simplifying ITEs.
 **/
#include "preproc/simp_ite.h"

namespace CVC4 {
namespace preproc {

SimpITEPass::SimpITEPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "simpITE", true) {}

/**
 * Ensures the assertions asserted after before now effectively come before
 *d_realAssertionsEnd.
 */
void SimpITEPass::compressBeforeRealAssertions(
    size_t before, AssertionPipeline* assertionsToPreprocess) {
  size_t curr = assertionsToPreprocess->size();
  if (before >= curr || assertionsToPreprocess->getRealAssertionsEnd() <= 0 ||
      assertionsToPreprocess->getRealAssertionsEnd() >= curr) {
    return;
  }
}

// Simplify ITE structure
PreprocessingPassResult SimpITEPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  spendResource(options::preprocessStep());
  unsigned numAssertionOnEntry = assertionsToPreprocess->size();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    spendResource(options::preprocessStep());
    Node result = d_theoryEngine->ppSimpITE((*assertionsToPreprocess)[i]);
    assertionsToPreprocess->replace(i, result);
    if (result.isConst() && !result.getConst<bool>()) {
      return CONFLICT;
    }
  }
  bool result = d_theoryEngine->donePPSimpITE(assertionsToPreprocess->ref());
  if (numAssertionOnEntry < assertionsToPreprocess->size()) {
    compressBeforeRealAssertions(numAssertionOnEntry, assertionsToPreprocess);
  }
  if (result) {
    return NO_CONFLICT;
  } else {
    return CONFLICT;
  }
}

}  // namespace preproc
}  // namespace CVC4
