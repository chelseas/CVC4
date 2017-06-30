#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__LINEAR_PREPROCESSING_PIPELINE_H
#define __CVC4__PREPROC__LINEAR_PREPROCESSING_PIPELINE_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

class LinearPreprocessingPipeline : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline *assertionsToPreprocess);
  LinearPreprocessingPipeline(const std::string &name,
                              const std::vector<PreprocessingPass *> &passes);

 private:
  std::vector<PreprocessingPass *> d_passes;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__LINEAR_PREPROCESSING_PIPELINE_H */
