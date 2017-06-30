/*********************                                                        */
/*! \file unconstrained_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for unconstrained simplification
 ** Preprocessing pass for unconstrained simplificiation.
 **/
#include "preproc/unconstrained_simp.h"

namespace CVC4 {
namespace preproc {

UnconstrainedSimpPass::UnconstrainedSimpPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "unconstrainedSimp", true) {}

PreprocessingPassResult UnconstrainedSimpPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  spendResource(options::preprocessStep());
  d_theoryEngine->ppUnconstrainedSimp(assertionsToPreprocess->ref());
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
