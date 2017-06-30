/*********************                                                        */
/*! \file early_theory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for early theory preprocessing
 **
 ** Preprocessing pass for early theory preprocessing.
 **/
#include "preproc/early_theory.h"

namespace CVC4 {
namespace preproc {

EarlyTheoryPreprocessingPass::EarlyTheoryPreprocessingPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "earlyTheory", true) {}

PreprocessingPassResult EarlyTheoryPreprocessingPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  // Call the theory preprocessors
  d_theoryEngine->preprocessStart();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Assert(theory::Rewriter::rewrite((*assertionsToPreprocess)[i]) ==
           (*assertionsToPreprocess)[i]);
    assertionsToPreprocess->replace(
        i, d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
    Assert(theory::Rewriter::rewrite((*assertionsToPreprocess)[i]) ==
           (*assertionsToPreprocess)[i]);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
