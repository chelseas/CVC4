#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include "expr/node.h"
#include <iostream>
#include <vector>
#include <string>
#include "smt/dump.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class PreprocessingPass {
 public:
  virtual void apply(std::vector<Node>* assertionsToPreprocess) = 0;
  void dumpAssertions(const char* key, const std::vector<Node>& assertionList) {
  if( Dump.isOn("assertions") &&
      Dump.isOn(std::string("assertions:") + key) ) {
    // Push the simplified assertions to the dump output stream
    for(unsigned i = 0; i < assertionList.size(); ++ i) {
      TNode n = assertionList[i];
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
      }
    }
  }

  PreprocessingPass(ResourceManager* resourceManager) : d_resourceManager(resourceManager) {
  }

private:
  ResourceManager* d_resourceManager;

protected: 
  void spendResource(unsigned amount) {
    d_resourceManager->spendResource(amount);
  }
  // TODO: modify class as needed
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
