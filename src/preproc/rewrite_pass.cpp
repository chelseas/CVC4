/*********************                                                        */
/*! \file rewrite_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that rewrite assertions
 **
 ** Preprocessing pass that rewrites assertion.
 **/
#include "preproc/rewrite_pass.h"

namespace CVC4 {
namespace preproc {

RewritePass::RewritePass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "rewrite", true) {}

PreprocessingPassResult RewritePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(
        i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
  }
  return NO_CONFLICT;
}

}  // preproc namespace
}  // CVC4 namespace
