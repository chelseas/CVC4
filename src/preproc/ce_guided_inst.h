/*********************                                                        */
/*! \file ce_guided_inst.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample guided instantiation
 **
 ** Implementation for counter example guided instantiation
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__CE_GUIDED_INST_H
#define __CVC4__PREPROC__CE_GUIDED_INST_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class CEGuidedInstPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  CEGuidedInstPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__CE_GUIDED_INST_H */
