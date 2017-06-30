/*********************                                                        */
/*! \file apply_substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that applies top level substitutions.
 **
 ** A preprocessing pass that applies top level substitutions to
 **  assertions
 **/

#include "preproc/apply_substitutions.h"

namespace CVC4 {
namespace preproc {

ApplySubstitutionsPass::ApplySubstitutionsPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "applySubstitutions", true) {}

PreprocessingPassResult ApplySubstitutionsPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Trace("simplify") << "applying to " << (*assertionsToPreprocess)[i]
                      << std::endl;
    spendResource(options::preprocessStep());
    assertionsToPreprocess->replace(
        i, theory::Rewriter::rewrite(
               assertionsToPreprocess->getTopLevelSubstitutions()->apply(
                   (*assertionsToPreprocess)[i])));
    Trace("simplify") << "  got " << (*assertionsToPreprocess)[i] << std::endl;
  }
  return NO_CONFLICT;
}

}  // preproc namespace
}  // CVC4 namespace
