/*********************                                                        */
/*! \file remove_ite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that removes ITEs
 **
 ** Preprocessing pass that removed ITEs.
 **/
#include "preproc/remove_ite.h"

namespace CVC4 {
namespace preproc {

RemoveITEPass::RemoveITEPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "removeITE", true),
      d_numAssertionsPre("preproc::numAssertionsPre", 0),
      d_numAssertionsPost("preproc::numAssertionsPost", 0) {}

RemoveITEPass::~RemoveITEPass() {
  Assert(smt::smtEngineInScope());
  if (smtStatisticsRegistry() != NULL) {
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPost);
  }
}

void RemoveITEPass::initInternal(PreprocessingPassAPI* api) {
  smtStatisticsRegistry()->registerStat(&d_numAssertionsPre);
  smtStatisticsRegistry()->registerStat(&d_numAssertionsPost);
}

/**
   * Remove ITEs from the assertions.
   */
PreprocessingPassResult RemoveITEPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_iteRemover = d_api->getIteRemover();
  // Remove ITEs, updating d_iteSkolemMap

  // statistics moved into removeITE
  d_numAssertionsPre += assertionsToPreprocess->size();

  d_api->finalOptionsAreSet();
  spendResource(options::preprocessStep());

  // Remove all of the ITE occurrences and normalize
  d_iteRemover->run(assertionsToPreprocess->ref(),
                    *assertionsToPreprocess->getSkolemMap(), true);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(
        i, theory::Rewriter::rewrite((*assertionsToPreprocess)[i]));
  }

  // statistics moved into removeITE pass
  d_numAssertionsPost += assertionsToPreprocess->size();

  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
