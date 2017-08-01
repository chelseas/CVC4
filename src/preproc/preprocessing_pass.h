#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include "expr/node.h"
#include <iostream>
#include <vector>
#include <string>

#include "preproc/preprocessing_pass_registry.h"
#include "smt/dump.h"
#include "decision/decision_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/substitutions.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_model.h"
#include "options/proof_options.h"
//#include "util/statistics_registry.h"
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
  
  AssertionPipeline() : d_realAssertionsEnd(0), d_iteSkolemMap(){
  }

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
 
  unsigned getRealAssertionsEnd() {
    return d_realAssertionsEnd;
  }
 
  void setRealAssertionsEnd(unsigned newVal) {
    d_realAssertionsEnd = newVal;
  }
  
  IteSkolemMap* getSkolemMap() {
    return &d_iteSkolemMap;
  } 

private:
  /** Size of assertions array when preprocessing starts */
  unsigned d_realAssertionsEnd;
  IteSkolemMap d_iteSkolemMap; 
};// class AssertionPipeline 

struct PreprocessingPassResult {
 bool d_noConflict;
 PreprocessingPassResult(bool noConflict) : d_noConflict(noConflict){
}
};

class PreprocessingPass {
 public:
/*  void init(){
  assert(!d_initialized); 
  smtStatisticsRegistry()->registerStat(&d_timer); 
 
  initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals)


  d_initialized = true;
  }*/

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
  if (n == NodeManager::currentNM()->mkConst(true)) {
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

 // TODO: instead of having a registerPass argument here, we should probably
  // have two different subclasses of PreprocessingPass or a superclass for
  // PreprocessingPass that does not do any registration.

 PreprocessingPass(const std::string& name, bool registerPass = false) : d_name(name), d_timer("preproc::" + name), d_initialized(false){
   if (registerPass) {
     PreprocessingPassRegistry::getInstance()->registerPass(this);
   }
//   smtStatisticsRegistry()->registerStat(&d_timer);
  }
 
 ~PreprocessingPass() {
//   assert(d_initialized);
//   smtStatisticsRegistry()->unregisterStat(&d_timer);
 }

private:

protected: 
 
  virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals) = 0;

 void spendResource(unsigned amount) {
    NodeManager::currentResourceManager()->spendResource(amount);
  }  // TODO: modify class as needed
  std::string d_name;
  TimerStat d_timer; 
  bool d_initialized;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
