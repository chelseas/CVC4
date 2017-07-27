#include "preproc/preprocessing_pass_registry.h"

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

void PreprocessingPassRegistry::registerPass(
    PreprocessingPass* preprocessingPass) {
  Debug("pp-registry") << "Registering pass" << std::endl;

  // TODO: Add pass to d_stringToPreprocessingPass map
}

PreprocessingPass* PreprocessingPassRegistry::getPass(
    const std::string& ppName) {
  return d_stringToPreprocessingPass[ppName];
}

}  // namespace preproc
}  // namespace CVC4
