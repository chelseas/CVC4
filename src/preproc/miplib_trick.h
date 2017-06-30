/*********************                                                        */
/*! \file miplib_trick.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for miplib trick pass.
 **
 ** Implementation for miplib trick pass.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__MIPLIB_TRICK_H
#define __CVC4__PREPROC__MIPLIB_TRICK_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class MiplibTrickPass : public PreprocessingPass {
 public:
  virtual void initInternal(PreprocessingPassAPI* api);
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  MiplibTrickPass(PreprocessingPassRegistry* registry);
  ~MiplibTrickPass();

 private:
  SmtEngine* d_smt;
  TheoryEngine* d_theoryEngine;
  LogicInfo d_logic;
  std::vector<Node>* d_boolVars;
  IntStat d_numMiplibAssertionsRemoved;
  theory::SubstitutionMap* d_topLevelSubstitutions;
  context::Context d_fakeContext;

  void traceBackToAssertions(const std::vector<Node>& nodes,
                             std::vector<TNode>& assertions,
                             AssertionPipeline* assertionsToPreprocess);
  size_t removeFromConjunction(
      Node& n, const std::unordered_set<unsigned long>& toRemove);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC_MIPLIB_TRICK_H */
