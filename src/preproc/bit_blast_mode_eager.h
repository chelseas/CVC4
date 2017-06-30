/*********************                                                        */
/*! \file bit_blast_mode_eager.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of add eager atoms pass..
 **
 ** Implementation of add eager atoms pass..
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__BIT_BLAST_MODE_EAGER_H
#define __CVC4__PREPROC__BIT_BLAST_MODE_EAGER_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class AddEagerAtomsPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  AddEagerAtomsPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_BIT_BLAST_MODE_EAGER_H */
