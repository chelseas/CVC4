/*********************                                                        */
/*! \file preprocessing_pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass super class
 **
 ** Implementation for preprocessing pass super class.
 **/
#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include <iostream>
#include <string>
#include <vector>
#include "expr/node.h"

#include "options/proof_options.h"
#include "preproc/preprocessing_pass_registry.h"
#include "smt/dump.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"
using namespace std;

namespace CVC4 {
namespace preproc {

/** Useful for counting the number of recursive calls. */
class ScopeCounter {
 private:
  unsigned& d_depth;

 public:
  ScopeCounter(unsigned& d) : d_depth(d) { ++d_depth; }
  ~ScopeCounter() { --d_depth; }
};

class AssertionPipeline {
  std::vector<Node> d_nodes;

 public:
  AssertionPipeline(context::Context* userContext)
      : d_realAssertionsEnd(0),
        d_iteSkolemMap(),
        d_nonClausalLearnedLiterals(),
        d_propagator(d_nonClausalLearnedLiterals, true, true),
        d_propagatorNeedsFinish(false),
        d_topLevelSubstitutions(userContext),
        d_substitutionsIndex(userContext, 0) {}

  size_t size() const { return d_nodes.size(); }

  void resize(size_t n) { d_nodes.resize(n); }
  void clear() {
    d_nonClausalLearnedLiterals.clear();
    d_iteSkolemMap.clear();
    d_nodes.clear();
  }

  Node& operator[](size_t i) { return d_nodes[i]; }
  const Node& operator[](size_t i) const { return d_nodes[i]; }
  void push_back(Node n) { d_nodes.push_back(n); }

  std::vector<Node>& ref() { return d_nodes; }
  const std::vector<Node>& ref() const { return d_nodes; }

  void replace(size_t i, Node n) {
    PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]););
    d_nodes[i] = n;
  }

  unsigned getRealAssertionsEnd() { return d_realAssertionsEnd; }

  void setRealAssertionsEnd(unsigned newVal) { d_realAssertionsEnd = newVal; }

  IteSkolemMap* getSkolemMap() { return &d_iteSkolemMap; }

  std::vector<Node>* getNonClausalLearnedLiterals() {
    return &d_nonClausalLearnedLiterals;
  }

  theory::booleans::CircuitPropagator* getPropagator() { return &d_propagator; }

  bool getPropagatorNeedsFinish() { return d_propagatorNeedsFinish; }

  void setPropagatorNeedsFinish(bool newVal) {
    d_propagatorNeedsFinish = newVal;
  }

  theory::SubstitutionMap* getTopLevelSubstitutions() {
    return &d_topLevelSubstitutions;
  }

  const theory::SubstitutionMap* getTopLevelSubstitutions() const {
    return &d_topLevelSubstitutions;
  }

  context::CDO<unsigned>* getSubstitutionsIndex() {
    return &d_substitutionsIndex;
  }

 private:
  /** Size of assertions array when preprocessing starts */
  unsigned d_realAssertionsEnd;
  IteSkolemMap d_iteSkolemMap;
  /** Learned literals */
  std::vector<Node> d_nonClausalLearnedLiterals;
  /** A circuit propagator for non-clausal propositional deduction */
  theory::booleans::CircuitPropagator d_propagator;
  bool d_propagatorNeedsFinish;
  /** The top level substitutions */
  theory::SubstitutionMap d_topLevelSubstitutions;
  /** Index for where to store substitutions */
  context::CDO<unsigned> d_substitutionsIndex;
};  // class AssertionPipeline

enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };

class PreprocessingPassRegistry;

class PreprocessingPass {
 public:
  void init(PreprocessingPassAPI* api);

  PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);

  void dumpAssertions(const char* key, const AssertionPipeline& assertionList);

  // TODO: instead of having a registerPass argument here, we should probably
  // have two different subclasses of PreprocessingPass or a superclass for
  // PreprocessingPass that does not do any registration.

  PreprocessingPass(PreprocessingPassRegistry* preprocessingPassRegistry,
                    const std::string& name, bool registerPass = false);

  virtual ~PreprocessingPass();

 protected:
  virtual void initInternal(PreprocessingPassAPI* api) {}

  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) = 0;

  void spendResource(unsigned amount);
  PreprocessingPassAPI* d_api;
  std::string d_name;
  TimerStat d_timer;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */
