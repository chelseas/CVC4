/*********************                                                        */
/*! \file sep_pre_skolem_emp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that rewrites for for theory sep
 ** Preprocessing pass that rewrites for theory sep.
 **/
#include "preproc/sep_pre_skolem_emp.h"
#include "theory/sep/theory_sep_rewriter.h"

namespace CVC4 {
namespace preproc {

SepPreSkolemEmpPass::SepPreSkolemEmpPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "sepPreSkolem", true) {}

PreprocessingPassResult SepPreSkolemEmpPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Node prev = (*assertionsToPreprocess)[i];
    Node next = theory::sep::TheorySepRewriter::preprocess(prev);
    if (next != prev) {
      assertionsToPreprocess->replace(i, theory::Rewriter::rewrite(next));
      Trace("sep-preprocess") << "*** Preprocess sep " << prev << std::endl;
      Trace("sep-preprocess") << "   ...got " << (*assertionsToPreprocess)[i]
                              << std::endl;
    }
  }
  return NO_CONFLICT;
}

}  // preproc namespace
}  // CVC4 namespace
