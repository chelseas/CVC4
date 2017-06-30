/*********************                                                        */
/*! \file pb_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for pb rewrite pass
 **
 ** Implementation for pb rewrite pass.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PB_REWRITE_PASS_H
#define __CVC4__PREPROC__PB_REWRITE_PASS_H

#include "preproc/preprocessing_pass.h"
#include "theory/arith/pseudoboolean_proc.h"

namespace CVC4 {
namespace preproc {

class PBRewritePass : public PreprocessingPass {
 public:
  virtual void initInternal(PreprocessingPassAPI* api);
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  PBRewritePass(PreprocessingPassRegistry* registry);

 private:
  std::unique_ptr<theory::arith::PseudoBooleanProcessor> d_pbsProcessor;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PB_REWRITE_H */
