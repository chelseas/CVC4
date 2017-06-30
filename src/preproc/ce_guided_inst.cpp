/*********************                                                        */
/*! \file ce_guided_inst.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass for counterexample guided instantiation
 **
 ** A preprocessing pass for counter example guided instantiation
 **/
#include "preproc/ce_guided_inst.h"
#include "theory/quantifiers/ce_guided_instantiation.h"

namespace CVC4 {
namespace preproc {

CEGuidedInstPass::CEGuidedInstPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "ceGuidedInst", true) {}

PreprocessingPassResult CEGuidedInstPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    d_theoryEngine->getQuantifiersEngine()
        ->getCegInstantiation()
        ->preregisterAssertion((*assertionsToPreprocess)[i]);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
