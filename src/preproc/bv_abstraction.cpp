/*********************                                                        */
/*! \file bv_abstraction.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that abstracts bit vectors.
 **
 ** Abstract common structure over small domains to UF
 **/

#include "preproc/bv_abstraction.h"
#include "options/bv_bitblast_mode.h"
#include "options/bv_options.h"

namespace CVC4 {
namespace preproc {

BVAbstractionPass::BVAbstractionPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "BVAbstraction", true) {}

PreprocessingPassResult BVAbstractionPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_theoryEngine = d_api->getTheoryEngine();
  std::vector<Node> new_assertions;
  bool changed = d_theoryEngine->ppBvAbstraction(assertionsToPreprocess->ref(),
                                                 new_assertions);
  // TODO: move ppBvAbstraction out of Theory Engine
  assertionsToPreprocess->ref().swap(new_assertions);
  // if we are using the lazy solver and the abstraction
  // applies, then UF symbols were introduced
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY && changed) {
    LogicRequest req(*d_smt);
    req.widenLogic(theory::THEORY_UF);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
