/*********************                                                        */
/*! \file solve_int_as_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass for solving ints as bit vectors
 ** Implementation for preprocessing pass for solving ints as bit vectors.
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__SOLVE_INT_AS_BV_H
#define __CVC4__PREPROC__SOLVE_INT_AS_BV_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;

class SolveIntAsBVPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  SolveIntAsBVPass(PreprocessingPassRegistry* registry);

 private:
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeMap& cache);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__SOLVE_INT_AS_BV_H */
