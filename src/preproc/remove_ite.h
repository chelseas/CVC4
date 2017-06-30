/*********************                                                        */
/*! \file remove_ite.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass that removes ITEs
 **
 ** Implementation for preprocessing pass that removes ITEs.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__REMOVE_ITE_PASS_H
#define __CVC4__PREPROC__REMOVE_ITE_PASS_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace preproc {

class RemoveITEPass : public PreprocessingPass {
 public:
  virtual void initInternal(PreprocessingPassAPI* api);
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  RemoveITEPass(PreprocessingPassRegistry* registry);
  ~RemoveITEPass();

 private:
  SmtEngine* d_smt;
  RemoveTermFormulas* d_iteRemover;
  IntStat d_numAssertionsPre;
  IntStat d_numAssertionsPost;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__REMOVE_ITE_PASS_H */
