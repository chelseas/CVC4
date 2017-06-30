/*********************                                                        */
/*! \file rewrite_apply_to_const.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass that applies rewrite to const
 **
 ** Implementation for preprocessing pass that applies rewrite to const.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__REWRITE_APPLY_TO_CONST_H
#define __CVC4__PREPROC__REWRITE_APPLY_TO_CONST_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
class RewriteApplyToConstPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  RewriteApplyToConstPass(PreprocessingPassRegistry* registry);

 private:
  Node rewriteApplyToConst(TNode n);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_REWRITE_APPLY_TO_CONST_H */
