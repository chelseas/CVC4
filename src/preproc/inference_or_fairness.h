/*********************                                                        */
/*! \file inference_or_fairness.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for inference or fairness pass
 **
 ** Implementation for inference or fairness pass.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__INFERENCE_OR_FAIRNESS_H
#define __CVC4__PREPROC__INFERENCE_OR_FAIRNESS_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class InferenceOrFairnessPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  InferenceOrFairnessPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
  SmtEngine* d_smt;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__INFERENCE_OR)FAIRNESS_H */
