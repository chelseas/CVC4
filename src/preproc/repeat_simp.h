/*********************                                                        */
/*! \file repeat_simp.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass that repeats simp
 **
 ** Implementation for preprocessing pass that repeats simp.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__REPEAT_SIMP_H
#define __CVC4__PREPROC__REPEAT_SIMP_H

#include "preproc/preprocessing_pass.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preproc {

class RepeatSimpPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  RepeatSimpPass(PreprocessingPassRegistry* registry);

 private:
  theory::SubstitutionMap* d_topLevelSubstitutions;
  void collectSkolems(TNode n, set<TNode>& skolemSet,
                      unordered_map<Node, bool, NodeHashFunction>& cache,
                      AssertionPipeline* assertionsToPreprocess);
  bool checkForBadSkolems(TNode n, TNode skolem,
                          unordered_map<Node, bool, NodeHashFunction>& cache,
                          AssertionPipeline* assertionsToPreprocess);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__REPEAT_SIMP_H */
