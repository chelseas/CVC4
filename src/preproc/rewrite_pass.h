/*********************                                                        */
/*! \file rewrite_pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass that rewrite assertions
 **
 ** Implementation for preprocessing pass that rewrites assertions.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__REWRITE_H
#define __CVC4__PREPROC__REWRITE_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

class RewritePass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  RewritePass(PreprocessingPassRegistry* registry);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__REWRITE_H */
