#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H
#define __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H

#include "preproc/preprocessing_pass.h"

namespace CVC4 {
namespace preproc {

typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
typedef std::hash_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
  
class NlExtPurifyPass : public PreprocessingPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess);
  NlExtPurifyPass(ResourceManager* resourceManager);
 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

// TODO: add classes for other preprocessing steps here
class SolveRealAsIntPass : public PreprocessingPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess);
  SolveRealAsIntPass(ResourceManager* resourceManager);
 private:
  Node realToInt(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

class SolveIntAsBVPass : public PreprocessingPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess);
  SolveIntAsBVPass(ResourceManager* resourceManager);
 private:
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeMap& cache); 
};

class BVToBoolPass : public PreprocessingPass {
 public:
   virtual void apply(std::vector<Node>* assertionsToPreprocess);
   BVToBoolPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine);
 private:
  // Lift bit-vectors of size 1 to booleans
  TheoryEngine* d_theoryEngine;
  void bvToBool(std::vector<Node>* assertionsToPreprocess);
};

class BoolToBVPass : public PreprocessingPass {
 public:
   virtual void apply(std::vector<Node>* assertionsTopreprocess);
   BoolToBVPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine);
 private:
   // Convert booleans to bit-vectors of size 1
  TheoryEngine* d_theoryEngine;
  void boolToBv(std::vector<Node>* assertionsToPreprocess);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
