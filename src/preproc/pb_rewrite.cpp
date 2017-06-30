/*********************                                                        */
/*! \file pb_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for pb rewrite pass
 **
 ** Preprocessing pass for pb rewrite pass.
 **/
#include "preproc/pb_rewrite.h"
#include "preproc/miplib_trick.h"

namespace CVC4 {
namespace preproc {

PBRewritePass::PBRewritePass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "pbRewrite", true) {}

void PBRewritePass::initInternal(PreprocessingPassAPI* api) {
  d_pbsProcessor.reset(
      new theory::arith::PseudoBooleanProcessor(api->getUserContext()));
}

PreprocessingPassResult PBRewritePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_pbsProcessor->learn(assertionsToPreprocess->ref());
  if (d_pbsProcessor->likelyToHelp()) {
    d_pbsProcessor->applyReplacements(assertionsToPreprocess->ref());
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
