/*********************                                                        */
/*! \file solve_real_as_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass for solving reals as ints
 ** Implementation for preprocessing pass for solving reals as ints.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__SOLVE_REAL_AS_INT_H
#define __CVC4__PREPROC__SOLVE_REAL_AS_INT_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;

class SolveRealAsIntPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  SolveRealAsIntPass(PreprocessingPassRegistry* registry);

 private:
  Node realToInt(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__SOLVE_REAL_AS_INT_H */
