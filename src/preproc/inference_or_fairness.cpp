/*********************                                                        */
/*! \file inference_or_fairness.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for inference or fairness
 **
 ** Preprocessing pass for inference or fairness
 **/
#include "preproc/inference_or_fairness.h"
#include "options/uf_options.h"

namespace CVC4 {
namespace preproc {

InferenceOrFairnessPass::InferenceOrFairnessPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "inferenceOrFairness", true) {}

PreprocessingPassResult InferenceOrFairnessPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_theoryEngine = d_api->getTheoryEngine();
  // sort inference technique
  SortInference* si = d_theoryEngine->getSortInference();
  si->simplify(assertionsToPreprocess->ref(), options::sortInference(),
               options::ufssFairnessMonotone());
  for (std::map<Node, Node>::iterator it = si->d_model_replace_f.begin();
       it != si->d_model_replace_f.end(); ++it) {
    d_smt->setPrintFuncInModel(it->first.toExpr(), false);
    d_smt->setPrintFuncInModel(it->second.toExpr(), true);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
