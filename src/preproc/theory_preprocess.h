/*********************                                                        */
/*! \file theory_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass for preprocessing theories
 ** Implementaiton for preprocessing pass for preprocessing theories.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__THEORY_PREPROCESS_H
#define __CVC4__PREPROC__THEORY_PREPROCESS_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class TheoryPreprocessPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  TheoryPreprocessPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_THEORY_PREPROCESS_H */
