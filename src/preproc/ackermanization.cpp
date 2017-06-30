/*********************                                                        */
/*! \file ackermanization.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that makes ackermanization assertions.
 **
 ** A preprocessing pass that makes ackermanization assertions.
 **/

#include "preproc/ackermanization.h"

namespace CVC4 {
namespace preproc {

AckermanizationPass::AckermanizationPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "ackermanization", true) {}

PreprocessingPassResult AckermanizationPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  d_theoryEngine->mkAckermanizationAssertions(assertionsToPreprocess->ref());
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
