/*********************                                                        */
/*! \file quantified.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of preprocessing pass that processes quantified
 *passes.
 **
 ** Implementation of preprocessing pass that processes quantified passes and
 *the fmf fun well defined flag.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__QUANTIFIED_PASS_H
#define __CVC4__PREPROC__QUANTIFIED_PASS_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class QuantifiedPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  QuantifiedPass(PreprocessingPassRegistry* registry);

 private:
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;
  TheoryEngine* d_theoryEngine;
  SmtEngine* d_smt;
  std::map<Node, TypeNode>* d_fmfRecFunctionsAbs;
  std::map<Node, std::vector<Node> >* d_fmfRecFunctionsConcrete;
  NodeList* d_fmfRecFunctionsDefined;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__QUANTIFIED_PASS_H */
