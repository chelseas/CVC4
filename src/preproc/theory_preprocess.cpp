/*********************                                                        */
/*! \file theory_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for preprocessing theories
 ** Preprocessing pass for preprocessing theories.
 **/
#include "preproc/theory_preprocess.h"

namespace CVC4 {
namespace preproc {

TheoryPreprocessPass::TheoryPreprocessPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "theoryPreprocess", true) {}

PreprocessingPassResult TheoryPreprocessPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  // Call the theory preprocessors
  d_theoryEngine->preprocessStart();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(
        i, d_theoryEngine->preprocess((*assertionsToPreprocess)[i]));
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
