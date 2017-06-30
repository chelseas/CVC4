/*********************                                                        */
/*! \file bv_to_bool.h_
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of bv to bool pass.
 **
 ** Lifts bit-vectors of size 1 to booleans.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__BV_TO_BOOL_H
#define __CVC4__PREPROC__BV_TO_BOOL_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class BVToBoolPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  BVToBoolPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__BV_TO_BOOL_H */
