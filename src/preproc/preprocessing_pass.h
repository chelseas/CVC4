#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include "expr/node.h"
#include <iostream>
#include <vector>
#include <string>

#include "preproc/preprocessing_pass_registry.h"
#include "smt/dump.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace std;

namespace CVC4 {

namespace preproc {

/** Useful for counting the number of recursive calls. */
class ScopeCounter {
private:
  unsigned& d_depth;
public:
  ScopeCounter(unsigned& d) : d_depth(d) {
    ++d_depth;
  }
  ~ScopeCounter(){
    --d_depth;
  }
};

class DefinedFunction {
  Node d_func;
  vector<Node> d_formals;
  Node d_formula;
public:
  DefinedFunction() {}
  DefinedFunction(Node func, vector<Node> formals, Node formula) :
    d_func(func),
    d_formals(formals),
    d_formula(formula) {
  }
  Node getFunction() const { return d_func; }
  vector<Node> getFormals() const { return d_formals; }
  Node getFormula() const { return d_formula; }
};
/* class DefinedFunction */

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

struct PreprocessingPassResult {
 bool d_noConflict;
 PreprocessingPassResult(bool noConflict) : d_noConflict(noConflict){
}
};

class PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess) = 0;
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

  // TODO: instead of having a registerPass argument here, we should probably
  // have two different subclasses of PreprocessingPass or a superclass for
  // PreprocessingPass that does not do any registration.
  PreprocessingPass(ResourceManager* resourceManager, bool registerPass = false)
      : d_resourceManager(resourceManager) {
    if (registerPass) {
      PreprocessingPassRegistry::getInstance()->registerPass(this);
    }
  }

private:
  ResourceManager* d_resourceManager;

protected: 
  void spendResource(unsigned amount) {
    d_resourceManager->spendResource(amount);
  }  // TODO: modify class as needed
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
