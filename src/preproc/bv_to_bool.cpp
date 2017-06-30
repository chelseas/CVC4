/*********************                                                        */
/*! \file bv_to_bool.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that converts bit vectors to bools
 **
 ** Lift bit-vectors of size 1 to booleans
 **/
#include "preproc/bv_to_bool.h"

namespace CVC4 {
namespace preproc {

BVToBoolPass::BVToBoolPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "BVToBool", true) {}

PreprocessingPassResult BVToBoolPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();

  Trace("bv-to-bool") << "SmtEnginePrivate::BVToBool()" << std::endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBvToBool(assertionsToPreprocess->ref(), new_assertions);
  // TODO: move ppBvToBool out of theoryEngine
  assertionsToPreprocess->ref().swap(new_assertions);
  return NO_CONFLICT;
}

}  // preproc namespace
}  // CVC4 namespace
