/*********************                                                        */
/*! \file linear_preprocessing_pipeline.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Linear preprocessing pipeline that processes passes linearly
 **
 ** Linear preprocessing pipeline iterates through a vector to apply
 *preprocessing passes.
 **/
#include "preproc/linear_preprocessing_pipeline.h"

namespace CVC4 {
namespace preproc {

LinearPreprocessingPipeline::LinearPreprocessingPipeline(
    const std::string& name, const std::vector<PreprocessingPass*>& passes)
    : PreprocessingPass(NULL, name), d_passes(passes) {}

PreprocessingPassResult LinearPreprocessingPipeline::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (PreprocessingPass* pass : d_passes) {
    assert(pass != NULL);
    pass->apply(assertionsToPreprocess);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
