/*********************                                                        */
/*! \file theory_proof_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for proving theories
 ** Preprocessing pass for proving theories.
 **/
#include "preproc/theory_proof_pass.h"

namespace CVC4 {
namespace preproc {

TheoryProofPass::TheoryProofPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "theoryProof", true) {}

PreprocessingPassResult TheoryProofPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    ProofManager::currentPM()->addAssertion(
        (*assertionsToPreprocess)[i].toExpr());
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
