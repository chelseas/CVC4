/*********************                                                        */
/*! \file preprocessing_pass_api.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass api for passes
 **
 ** Preprocessing pass api for passes. Takes in variables and methods from d_smt
 *and d_private and allows for access to the passes.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_API_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_API_H

#include <string>
#include "decision/decision_engine.h"
#include "smt/smt_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class DefinedFunction {
  Node d_func;
  vector<Node> d_formals;
  Node d_formula;

 public:
  DefinedFunction() {}
  DefinedFunction(Node func, vector<Node> formals, Node formula)
      : d_func(func), d_formals(formals), d_formula(formula) {}
  Node getFunction() const { return d_func; }
  vector<Node> getFormals() const { return d_formals; }
  Node getFormula() const { return d_formula; }
};
/* class DefinedFunction */

typedef context::CDHashMap<Node, preproc::DefinedFunction, NodeHashFunction>
    DefinedFunctionMap;

class PreprocessingPassAPI {
 public:
  PreprocessingPassAPI(SmtEngine* smt) : d_smt(smt) {}

  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->d_theoryEngine; }
  LogicInfo getLogic() { return d_smt->d_logic; }
  RemoveTermFormulas* getIteRemover() { return d_smt->getIteRemover(); }
  DecisionEngine* getDecisionEngine() { return d_smt->d_decisionEngine; }
  prop::PropEngine* getPropEngine() { return d_smt->d_propEngine; }
  std::vector<Node>* getBoolVars() { return d_smt->getBoolVars(); }
  std::map<Node, TypeNode>* getFmfRecFunctionsAbs() {
    return &d_smt->d_fmfRecFunctionsAbs;
  }
  std::map<Node, std::vector<Node> >* getFmfRecFunctionsConcrete() {
    return &d_smt->d_fmfRecFunctionsConcrete;
  }
  SmtEngine::NodeList* getFmfRecFunctionsDefined() {
    return d_smt->d_fmfRecFunctionsDefined;
  }
  context::Context* getUserContext() { return d_smt->d_userContext; }
  context::Context* getContext() { return d_smt->d_context; }
  void finalOptionsAreSet() { return d_smt->finalOptionsAreSet(); }
  void addFormula(TNode n, bool inUnsatCore,
                  bool inInput = true) throw(TypeCheckingException,
                                             LogicException) {
    return d_smt->addFormula(n, inUnsatCore, inInput);
  }
  bool isDefinedFunction(Node func) {
    return d_smt->d_definedFunctions->find(func) !=
           d_smt->d_definedFunctions->end();
  }
  const DefinedFunction getDefinedFunction(TNode func) {
    SmtEngine::DefinedFunctionMap::const_iterator i =
        d_smt->d_definedFunctions->find(func);
    return (*i).second;
  }

 private:
  SmtEngine* d_smt;
};  // class PreprocessingPassAPI

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_API_H */
