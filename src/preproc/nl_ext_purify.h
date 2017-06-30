/*********************                                                        */
/*! \file nl_ext_purify.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for nl ext pass
 **
 ** Implementation for nl ext pass.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__NL_EXT_PURIFY_H
#define __CVC4__PREPROC__NL_EXT_PURIFY_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;

class NlExtPurifyPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  NlExtPurifyPass(PreprocessingPassRegistry* registry);

 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__NL_EXT_PURIFY_H */
