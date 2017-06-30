/*********************                                                        */
/*! \file bool_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that converts bool to bv.
 **
 ** A preprocessing pass that converts bool to bv.
 **/

#include "preproc/bool_to_bv.h"

namespace CVC4 {
namespace preproc {

BoolToBVPass::BoolToBVPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "boolToBV", true) {}

PreprocessingPassResult BoolToBVPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_theoryEngine->ppBoolToBv(assertionsToPreprocess->ref(), new_assertions);
  // TODO: move ppBoolToBV out of theoryEngine
  assertionsToPreprocess->ref().swap(new_assertions);
  return NO_CONFLICT;
}

}  // preproc namespace
}  // CVC4 namespace
