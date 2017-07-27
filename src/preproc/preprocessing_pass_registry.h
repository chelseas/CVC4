#include "cvc4_private.h"

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

  void registerPass(PreprocessingPass* preprocessingPass);
  PreprocessingPass* getPass(const std::string& ppName);

 private:
  static std::unique_ptr<PreprocessingPassRegistry> s_instance;

  std::unordered_map<std::string, PreprocessingPass*>
      d_stringToPreprocessingPass;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H */
