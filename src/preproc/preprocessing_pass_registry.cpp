#include "preproc/preprocessing_pass_registry.h"
#include "preproc/preprocessing_pass.h"
#include "base/output.h"

namespace CVC4 {
namespace preproc {

std::unique_ptr<PreprocessingPassRegistry>
    PreprocessingPassRegistry::s_instance = nullptr;

PreprocessingPassRegistry* PreprocessingPassRegistry::getInstance() {
  if (!s_instance) {
    s_instance.reset(new PreprocessingPassRegistry());
  }
  return s_instance.get();
}

void PreprocessingPassRegistry::init(
     SmtEngine* smt, TheoryEngine* theoryEngine,
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals)  {
  for(std::pair<std::string, PreprocessingPass*> element : d_stringToPreprocessingPass) {
     element.second->init(smt, theoryEngine, topLevelSubstitutions, pbsProcessor, iteRemover, decisionEngine, propEngine, propagatorNeedsFinish, propagator, boolVars, substitutionsIndex, nonClausalLearnedLiterals);
  }
}

void PreprocessingPassRegistry::registerPass(const std::string& ppName,
    PreprocessingPass* preprocessingPass) {
  Debug("pp-registry") << "Registering pass" << std::endl;
  d_stringToPreprocessingPass[ppName] = preprocessingPass;
}

PreprocessingPass* PreprocessingPassRegistry::getPass(
    const std::string& ppName) {
  assert(d_stringToPreprocessingPass.find(ppName) != d_stringToPreprocessingPass.end());
  return d_stringToPreprocessingPass[ppName];
}

}  // namespace preproc
}  // namespace CVC4
