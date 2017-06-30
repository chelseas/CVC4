/*********************                                                        */
/*! \file non_clausal_simplification.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass for non clausal simlpification pass
 **
 ** Preprocessing pass for non clausal simlpification pass.
 **/
#include "preproc/non_clausal_simplification.h"

namespace CVC4 {
namespace preproc {

/**
  * Runs the nonclausal solver and tries to solve all the assigned
  * theory literals.
  *
  * Returns false if the formula simplifies to "false"
  */
NonClausalSimplificationPass::NonClausalSimplificationPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "nonClausalSimplification", true),
      d_numConstantProps("preproc::d_numConstantProps", 0) {}

NonClausalSimplificationPass::~NonClausalSimplificationPass() {
  Assert(smt::smtEngineInScope());
  if (smtStatisticsRegistry() != NULL) {
    smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
  }
}

void NonClausalSimplificationPass::initInternal(PreprocessingPassAPI* api) {
  smtStatisticsRegistry()->registerStat(&d_numConstantProps);
}

// returns false if it learns a conflict
PreprocessingPassResult NonClausalSimplificationPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_smt = d_api->getSmt();
  d_theoryEngine = d_api->getTheoryEngine();
  d_context = d_api->getContext();
  spendResource(options::preprocessStep());
  d_api->finalOptionsAreSet();

  if (options::unsatCores() || options::fewerPreprocessingHoles()) {
    return NO_CONFLICT;
  }

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Trace("simplify") << "Assertion #" << i << " : "
                      << (*assertionsToPreprocess)[i] << std::endl;
  }

  if (assertionsToPreprocess->getPropagatorNeedsFinish()) {
    assertionsToPreprocess->getPropagator()->finish();
    assertionsToPreprocess->setPropagatorNeedsFinish(false);
  }
  assertionsToPreprocess->getPropagator()->initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Assert(theory::Rewriter::rewrite((*assertionsToPreprocess)[i]) ==
           (*assertionsToPreprocess)[i]);
    // Don't reprocess substitutions
    if (*(assertionsToPreprocess->getSubstitutionsIndex()) > 0 &&
        i == *(assertionsToPreprocess->getSubstitutionsIndex())) {
      continue;
    }
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting "
                      << (*assertionsToPreprocess)[i] << endl;
    Debug("cores") << "d_propagator assertTrue: "
                   << (*assertionsToPreprocess)[i] << std::endl;
    assertionsToPreprocess->getPropagator()->assertTrue(
        (*assertionsToPreprocess)[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (assertionsToPreprocess->getPropagator()->propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    assertionsToPreprocess->clear();
    d_api->addFormula(falseNode, false, false);
    assertionsToPreprocess->setPropagatorNeedsFinish(true);
    return CONFLICT;
  }

  Trace("simplify")
      << "Iterate through "
      << assertionsToPreprocess->getNonClausalLearnedLiterals()->size()
      << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  theory::SubstitutionMap constantPropagations(d_context);
  theory::SubstitutionMap newSubstitutions(d_context);
  theory::SubstitutionMap::iterator pos;
  unsigned j = 0;
  for (unsigned
           i = 0,
           i_end =
               assertionsToPreprocess->getNonClausalLearnedLiterals()->size();
       i < i_end; ++i) {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral =
        (*(assertionsToPreprocess->getNonClausalLearnedLiterals()))[i];
    Assert(theory::Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(
               learnedLiteral) == learnedLiteral);
    Trace("simplify") << "Process learnedLiteral : " << learnedLiteral
                      << std::endl;
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew) {
      learnedLiteral = theory::Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after newSubs : "
                      << learnedLiteral << std::endl;
    for (;;) {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral) {
        break;
      }
      ++d_numConstantProps;
      learnedLiteral = theory::Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after constProp : "
                      << learnedLiteral << std::endl;
    // It might just simplify to a constant
    if (learnedLiteral.isConst()) {
      if (learnedLiteral.getConst<bool>()) {
        // If the learned literal simplifies to true, it's redundant
        continue;
      } else {
        // If the learned literal simplifies to false, we're in conflict
        Trace("simplify")
            << "SmtEnginePrivate::nonClausalSimplify(): "
            << "conflict with "
            << (*(assertionsToPreprocess->getNonClausalLearnedLiterals()))[i]
            << endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        d_api->addFormula(NodeManager::currentNM()->mkConst<bool>(false), false,
                          false);
        assertionsToPreprocess->setPropagatorNeedsFinish(true);
        return CONFLICT;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "solving " << learnedLiteral << endl;

    theory::Theory::PPAssertStatus solveStatus =
        d_theoryEngine->solve(learnedLiteral, newSubstitutions);

    switch (solveStatus) {
      case theory::Theory::PP_ASSERT_STATUS_SOLVED: {
        // The literal should rewrite to true
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "solved " << learnedLiteral << endl;
        Assert(theory::Rewriter::rewrite(newSubstitutions.apply(learnedLiteral))
                   .isConst());
        //        vector<pair<Node, Node> > equations;
        //        constantPropagations.simplifyLHS(d_topLevelSubstitutions,
        //        equations, true);
        //        if (equations.empty()) {
        //          break;
        //        }
        //        Assert(equations[0].first.isConst() &&
        //        equations[0].second.isConst() && equations[0].first !=
        //        equations[0].second);
        // else fall through
        break;
      }
      case theory::Theory::PP_ASSERT_STATUS_CONFLICT:
        // If in conflict, we return false
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict while solving " << learnedLiteral
                          << endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        d_api->addFormula(NodeManager::currentNM()->mkConst<bool>(false), false,
                          false);
        assertionsToPreprocess->setPropagatorNeedsFinish(true);
        return CONFLICT;
      default:
        // removed d_doConstantProp
        if (learnedLiteral.getKind() == kind::EQUAL &&
            (learnedLiteral[0].isConst() || learnedLiteral[1].isConst())) {
          // constant propagation
          TNode t;
          TNode c;
          if (learnedLiteral[0].isConst()) {
            t = learnedLiteral[1];
            c = learnedLiteral[0];
          } else {
            t = learnedLiteral[0];
            c = learnedLiteral[1];
          }
          Assert(!t.isConst());
          Assert(constantPropagations.apply(t) == t);
          Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(t) ==
                 t);
          Assert(newSubstitutions.apply(t) == t);
          constantPropagations.addSubstitution(t, c);
          // vector<pair<Node,Node> > equations;
          // constantPropagations.simplifyLHS(t, c, equations, true);
          // if (!equations.empty()) {
          //   Assert(equations[0].first.isConst() &&
          //   equations[0].second.isConst() && equations[0].first !=
          //   equations[0].second);
          //   d_assertions.clear();
          //   addFormula(NodeManager::currentNM()->mkConst<bool>(false), false,
          //   false);
          //   return;
          // }
          // d_topLevelSubstitutions.simplifyRHS(constantPropagations);
        } else {
          // Keep the literal
          (*(assertionsToPreprocess->getNonClausalLearnedLiterals()))[j++] =
              (*(assertionsToPreprocess->getNonClausalLearnedLiterals()))[i];
        }
        break;
    }
  }

#ifdef CVC4_ASSERTIONS
  // NOTE: When debugging this code, consider moving this check inside of the
  // loop over d_nonClausalLearnedLiterals. This check has been moved outside
  // because it is costly for certain inputs (see bug 508).
  //
  // Check data structure invariants:
  // 1. for each lhs of d_topLevelSubstitutions, does not appear anywhere in rhs
  // of d_topLevelSubstitutions or anywhere in constantPropagations
  // 2. each lhs of constantPropagations rewrites to itself
  // 3. if l -> r is a constant propagation and l is a subterm of l' with l' ->
  // r' another constant propagation, then l'[l/r] -> r' should be a
  //    constant propagation too
  // 4. each lhs of constantPropagations is different from each rhs
  for (pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos) {
    Assert((*pos).first.isVar());
    Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(
               (*pos).first) == (*pos).first);
    Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(
               (*pos).second) == (*pos).second);
    Assert(newSubstitutions.apply(newSubstitutions.apply((*pos).second)) ==
           newSubstitutions.apply((*pos).second));
  }
  for (pos = constantPropagations.begin(); pos != constantPropagations.end();
       ++pos) {
    Assert((*pos).second.isConst());
    Assert(theory::Rewriter::rewrite((*pos).first) == (*pos).first);
    // Node newLeft = d_topLevelSubstitutions.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) &&
    //          constantPropagations.apply(newLeft) == (*pos).second));
    // }
    // newLeft = constantPropagations.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) &&
    //          constantPropagations.apply(newLeft) == (*pos).second));
    // }
    Assert(constantPropagations.apply((*pos).second) == (*pos).second);
  }
#endif  // CVC4_ASSERTIONS

  // Resize the learnt
  Trace("simplify") << "Resize non-clausal learned literals to " << j
                    << std::endl;
  assertionsToPreprocess->getNonClausalLearnedLiterals()->resize(j);

  unordered_set<TNode, TNodeHashFunction> s;
  Trace("debugging") << "NonClausal simplify pre-preprocess\n";
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Node assertion = (*assertionsToPreprocess)[i];
    Node assertionNew = newSubstitutions.apply(assertion);
    Trace("debugging") << "assertion = " << assertion << endl;
    Trace("debugging") << "assertionNew = " << assertionNew << endl;
    if (assertion != assertionNew) {
      assertion = theory::Rewriter::rewrite(assertionNew);
      Trace("debugging") << "rewrite(assertion) = " << assertion << endl;
    }
    Assert(theory::Rewriter::rewrite(assertion) == assertion);
    for (;;) {
      assertionNew = constantPropagations.apply(assertion);
      if (assertionNew == assertion) {
        break;
      }
      ++d_numConstantProps;
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
      assertion = theory::Rewriter::rewrite(assertionNew);
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
    }
    Trace("debugging") << "\n";
    s.insert(assertion);
    assertionsToPreprocess->replace(i, assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: " << assertion << endl;
  }

  // If in incremental mode, add substitutions to the list of assertions
  if (*(assertionsToPreprocess->getSubstitutionsIndex()) > 0) {
    NodeBuilder<> substitutionsBuilder(kind::AND);
    substitutionsBuilder << (*assertionsToPreprocess)[*(
        assertionsToPreprocess->getSubstitutionsIndex())];
    pos = newSubstitutions.begin();
    for (; pos != newSubstitutions.end(); ++pos) {
      // Add back this substitution as an assertion
      TNode lhs = (*pos).first, rhs = newSubstitutions.apply((*pos).second);
      Node n = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
      substitutionsBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will "
                           "notify SAT layer of substitution: "
                        << n << endl;
    }
    if (substitutionsBuilder.getNumChildren() > 1) {
      assertionsToPreprocess->replace(
          *(assertionsToPreprocess->getSubstitutionsIndex()),
          theory::Rewriter::rewrite(Node(substitutionsBuilder)));
    }
  } else {
    // If not in incremental mode, must add substitutions to model
    theory::TheoryModel* m = d_theoryEngine->getModel();
    if (m != NULL) {
      for (pos = newSubstitutions.begin(); pos != newSubstitutions.end();
           ++pos) {
        Node n = (*pos).first;
        Node v = newSubstitutions.apply((*pos).second);
        Trace("model") << "Add substitution : " << n << " " << v << endl;
        m->addSubstitution(n, v);
      }
    }
  }

  NodeBuilder<> learnedBuilder(kind::AND);
  Assert(assertionsToPreprocess->getRealAssertionsEnd() <=
         assertionsToPreprocess->size());
  learnedBuilder << (*assertionsToPreprocess)
          [assertionsToPreprocess->getRealAssertionsEnd() - 1];

  for (unsigned i = 0;
       i < assertionsToPreprocess->getNonClausalLearnedLiterals()->size();
       ++i) {
    Node learned =
        (*(assertionsToPreprocess->getNonClausalLearnedLiterals()))[i];
    Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(learned) ==
           learned);
    Node learnedNew = newSubstitutions.apply(learned);
    if (learned != learnedNew) {
      learned = theory::Rewriter::rewrite(learnedNew);
    }
    Assert(theory::Rewriter::rewrite(learned) == learned);
    for (;;) {
      learnedNew = constantPropagations.apply(learned);
      if (learnedNew == learned) {
        break;
      }
      ++d_numConstantProps;
      learned = theory::Rewriter::rewrite(learnedNew);
    }
    if (s.find(learned) != s.end()) {
      continue;
    }
    s.insert(learned);
    learnedBuilder << learned;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal learned : " << learned << endl;
  }
  assertionsToPreprocess->getNonClausalLearnedLiterals()->clear();

  for (pos = constantPropagations.begin(); pos != constantPropagations.end();
       ++pos) {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(assertionsToPreprocess->getTopLevelSubstitutions()->apply(cProp) ==
           cProp);
    Node cPropNew = newSubstitutions.apply(cProp);
    if (cProp != cPropNew) {
      cProp = theory::Rewriter::rewrite(cPropNew);
      Assert(theory::Rewriter::rewrite(cProp) == cProp);
    }
    if (s.find(cProp) != s.end()) {
      continue;
    }
    s.insert(cProp);
    learnedBuilder << cProp;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal constant propagation : " << cProp << endl;
  }

  // Add new substitutions to topLevelSubstitutions
  // Note that we don't have to keep rhs's in full solved form
  // because SubstitutionMap::apply does a fixed-point iteration when
  // substituting
  assertionsToPreprocess->getTopLevelSubstitutions()->addSubstitutions(
      newSubstitutions);

  if (learnedBuilder.getNumChildren() > 1) {
    assertionsToPreprocess->replace(
        assertionsToPreprocess->getRealAssertionsEnd() - 1,
        theory::Rewriter::rewrite(Node(learnedBuilder)));
  }

  assertionsToPreprocess->setPropagatorNeedsFinish(true);
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
