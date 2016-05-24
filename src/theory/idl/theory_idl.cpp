/*********************                                                        */
/*! \file theory_idl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/idl/theory_idl.h"

#include <set>
#include <queue>

#include "options/idl_options.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace idl {

TheoryIdl::TheoryIdl(context::Context* c,
                     context::UserContext* u,
                     OutputChannel& out,
                     Valuation valuation,
                     const LogicInfo& logicInfo)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo),
      d_varMap(c),
      d_varList(c),
      d_numVars(0)
{}

void TheoryIdl::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Debug("theory::idl::vars")
        << "TheoryIdl::preRegisterTerm(): processing var " << node << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void TheoryIdl::presolve()
{
  d_numVars = d_varMap.size();
  Debug("theory::idl") << "TheoryIdl::preSolve(): d_numVars = " << d_numVars
                       << std::endl;

  // Initialize adjacency matrix.
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix.emplace_back(std::vector<Rational>(d_numVars));
    d_valid.emplace_back(std::vector<bool>(d_numVars, false));
  }
}

void TheoryIdl::postsolve()
{
  Debug("theory::idl") << "TheoryIdl::postSolve()" << std::endl;
}

Node TheoryIdl::ppRewrite(TNode atom) {
  Debug("theory::idl::rewrite")
      << "TheoryIdl::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  switch (atom.getKind())
  {
    case kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConst(-right);
      Node r_le_l = nm->mkNode(kind::LEQ, negated_left, negated_right);
      return nm->mkNode(kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case kind::LT:
    case kind::LEQ:
    case kind::GT:
    case kind::GEQ:
    case kind::NOT:
    // -------------------------------------------------------------------------

    default: break;
  }
  return atom;
}

void TheoryIdl::check(Effort level) {
  if (!fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  // Reset the graph
  for (size_t i = 0; i < d_numVars; i++)
  {
    for (size_t j = 0; j < d_numVars; j++)
    {
      d_valid[i][j] = false;
    }
  }

  for (assertions_iterator i = facts_begin(); i != facts_end(); ++i)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would use `Theory::get()` to
    // only get new assertions.
    Assertion assertion = (*i);
    Debug("theory::idl") << "TheoryIdl::check(): processing "
                         << assertion.assertion << std::endl;
    processAssertion(assertion.assertion);
  }

  if (negativeCycle())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder<> conjunction(kind::AND);
    for (assertions_iterator i = facts_begin(); i != facts_end(); ++i)
    {
      conjunction << (*i).assertion;
    }
    Node conflict = conjunction;
    d_out->conflict(conflict);
    return;
  }
}

bool TheoryIdl::collectModelInfo(TheoryModel* m)
{
  std::vector<Rational> distance(d_numVars, Rational(0));

  // ---------------------------------------------------------------------------
  // TODO: implement model generation by computing the single-source shortest
  // path from a node that has distance zero to all other nodes
  // ---------------------------------------------------------------------------

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConst(distance[i]), true);
  }

  return true;
}

void TheoryIdl::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == kind::LEQ);
  Assert(atom[0].getKind() == kind::MINUS);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == kind::UMINUS)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  d_valid[index1][index2] = true;
  d_matrix[index1][index2] = value;
}

bool TheoryIdl::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  return false;
}

void TheoryIdl::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                            const std::vector<std::vector<bool>>& valid)
{
  cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    cout << setw(6) << d_varList[j];
  }
  cout << endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    cout << setw(6) << d_varList[i];
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        cout << setw(6) << matrix[i][j];
      }
      else
      {
        cout << setw(6) << "oo";
      }
    }
    cout << endl;
  }
}

} /* namepsace CVC4::theory::idl */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */
