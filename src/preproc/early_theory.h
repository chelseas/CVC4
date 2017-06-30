/*********************                                                        */
/*! \file early_theory.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for early theory preprocessing
 **
 ** Implementation for early theory preprocessing.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__EARLY_THEORY_H
#define __CVC4__PREPROC__EARLY_THEORY_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class EarlyTheoryPreprocessingPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  EarlyTheoryPreprocessingPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_EARLY_THEORY_H */
