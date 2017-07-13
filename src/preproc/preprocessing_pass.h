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
class AssertionPipeline {
  std::vector<Node> d_nodes;

public:

  size_t size() const { return d_nodes.size(); }

  void resize(size_t n) { d_nodes.resize(n); }
  void clear() { d_nodes.clear(); }

  Node& operator[](size_t i) { return d_nodes[i]; }
  const Node& operator[](size_t i) const { return d_nodes[i]; }
  void push_back(Node n) { d_nodes.push_back(n); }

  std::vector<Node>& ref() { return d_nodes; }
  const std::vector<Node>& ref() const { return d_nodes; }

  void replace(size_t i, Node n) {
    PROOF( ProofManager::currentPM()->addDependence(n, d_nodes[i]); );
    d_nodes[i] = n;
  }
};// class AssertionPipeline 

class PreprocessingPass {
 public:
  virtual void apply(AssertionPipeline* assertionsToPreprocess) = 0;
  void dumpAssertions(const char* key, const AssertionPipeline& assertionList) {
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
