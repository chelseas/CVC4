/*********************                                                        */
/*! \file sep_pre_skolem_emp.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass that rewrites for for theory
 *sep
 ** Implementation for preprocessing pass that rewrites for theory sep.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__SEP_PRE_SKOLEM_EMP_H
#define __CVC4__PREPROC__SEP_PRE_SKOLEM_EMP_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

class SepPreSkolemEmpPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  SepPreSkolemEmpPass(PreprocessingPassRegistry* registry);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__SEP_PRE_SKOLEM_EMP_H */
