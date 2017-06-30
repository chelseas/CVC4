/*********************                                                        */
/*! \file apply_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of apply substitution passs.
 **
 ** Implementation of apply substitution pass.
 **/

#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__APPLY_SUBSTITUTIONS_H
#define __CVC4__PREPROC__APPLY_SUBSTITUTIONS_H

#include "preproc/preprocessing_pass.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preproc {

class ApplySubstitutionsPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  ApplySubstitutionsPass(PreprocessingPassRegistry* registry);

 private:
  theory::SubstitutionMap* d_topLevelSubstitutions;
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__APPLY_SUBSTITUTIONS_H */
