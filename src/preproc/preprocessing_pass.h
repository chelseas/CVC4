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
#include "theory/theory_model.h"
#include "options/proof_options.h"

using namespace std;

namespace CVC4 {

using namespace theory;

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

  void addFormula(TNode n, bool inUnsatCore, AssertionPipeline* assertionsToPreprocess, bool inInput = true)
   throw(TypeCheckingException, LogicException) {
  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << "), inUnsatCore = " << inUnsatCore << ", inInput = " << inInput << endl;

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {

        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
    // rewrite rules are by default in the unsat core because
    // they need to be applied until saturation
    if(options::unsatCores() &&
       n.getKind() == kind::REWRITE_RULE ){
      ProofManager::currentPM()->addUnsatCore(n.toExpr());
    }
  );

  // Add the normalized formula to the queue
  assertionsToPreprocess->push_back(n);
  //d_assertions.push_back(Rewriter::rewrite(n));
  }

  PreprocessingPass(ResourceManager* resourceManager) : d_resourceManager(resourceManager) {
  }

  PreprocessingPass(ResourceManager* resourceManager, Node dtrue) : d_resourceManager(resourceManager), d_true(dtrue){
  }

private:
  ResourceManager* d_resourceManager;

protected: 
  void spendResource(unsigned amount) {
    d_resourceManager->spendResource(amount);
  }  // TODO: modify class as needed
  Node d_true;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
