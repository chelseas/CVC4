#include "cvc4_private.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "decision/decision_engine.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H

#include <memory>
#include <string>
#include <unordered_map>

namespace CVC4 {
namespace preproc {

class PreprocessingPass;

class PreprocessingPassRegistry {
 public:
  static PreprocessingPassRegistry* getInstance();
  void init(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  void registerPass(const std::string& ppName, PreprocessingPass* preprocessingPass);
  PreprocessingPass* getPass(const std::string& ppName);

 private:
  static std::unique_ptr<PreprocessingPassRegistry> s_instance;

  std::unordered_map<std::string, PreprocessingPass*>
      d_stringToPreprocessingPass;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H */
