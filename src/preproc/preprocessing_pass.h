#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include "expr/node.h"

#include <vector>

namespace CVC4 {
namespace preproc {

class PreprocessingPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess) = 0;

  // TODO: modify class as needed
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
