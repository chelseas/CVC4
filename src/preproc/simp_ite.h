/*********************                                                        */
/*! \file simp_ite.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass for simplifying ITEs
 ** Implementaiton for preprocessing pass for simplifying ITEs.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__SIMP_ITE_H
#define __CVC4__PREPROC__SIMP_ITE_H

#include "preproc/preprocessing_pass.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class SimpITEPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  SimpITEPass(PreprocessingPassRegistry* registry);

 private:
  TheoryEngine* d_theoryEngine;
  void compressBeforeRealAssertions(size_t before,
                                    AssertionPipeline* assertionsToPreprocess);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_SIMP_ITE_H */
