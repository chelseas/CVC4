/*********************                                                        */
/*! \file do_static_learning.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass for static learning on the assertions
 **
 ** Performs static learning on the assertions.
 **/

#include "preproc/do_static_learning.h"

namespace CVC4 {
namespace preproc {

StaticLearningPass::StaticLearningPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "staticLearning", true) {}

PreprocessingPassResult StaticLearningPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_theoryEngine = d_api->getTheoryEngine();
  d_api->finalOptionsAreSet();
  spendResource(options::preprocessStep());

  Trace("simplify") << "SmtEnginePrivate::staticLearning()" << std::endl;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    NodeBuilder<> learned(kind::AND);
    learned << (*assertionsToPreprocess)[i];
    d_theoryEngine->ppStaticLearn((*assertionsToPreprocess)[i], learned);
    if (learned.getNumChildren() == 1) {
      learned.clear();
    } else {
      assertionsToPreprocess->replace(i, learned);
    }
  }
  // Perform static learning
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
