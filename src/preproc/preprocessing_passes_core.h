#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H
#define __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;

class NlExtPurifyPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess);

 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

// TODO: add classes for other preprocessing steps here

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
