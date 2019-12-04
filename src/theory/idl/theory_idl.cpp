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

  // assume at most 1 unary minus (no nested unary minuses)
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

    case kind::LT:
    {
      if(atom[0].getKind() == kind::MINUS)
      {
        // if(atom[1].getKind() == kind::UMINUS)
        // {
        //   const Rational& neg_n = atom[1][0].getConst<Rational>()
        //   Node n_minus_1 = -neg_n - Rational(1));
        // }
        // else // assume constant
        // {
          Node n_minus_1 = nm->mkConst(atom[1].getConst<Rational>() - Rational(1));
        // }
        return nm->mkNode(kind::LEQ, atom[0], n_minus_1);
      }
      else if (atom[1].getKind() == kind::MINUS)
      {
        Node negated_diff = nm->mkNode(kind::MINUS, atom[1][1], atom[1][0]);
        const Rational& n = atom[0].getConst<Rational>();
        Node negated_n_minus1 = nm->mkConst(-n - Rational(1));
        return nm->mkNode(kind::LEQ, negated_diff, negated_n_minus1);
      }
      else // neither side is a difference, assume we are dealing with the case of (< (x y))
      {
        // (x < y) -> (x - y < 0) -> (x - y <= -1)
        Node diff = nm->mkNode(kind::MINUS, atom[0], atom[1]);
        Node n = nm->mkConst(Rational(-1));
        return nm->mkNode(kind::LEQ, diff, n);
      }
      
    }
    case kind::LEQ:
    {
      if(atom[0].getKind() == kind::MINUS)
      {
        return nm->mkNode(kind::LEQ, atom[0], atom[1]);
      }
      else if(atom[1].getKind() == kind::MINUS)
      {
        Node negated_diff = nm->mkNode(kind::MINUS, atom[1][1], atom[1][0]);
        const Rational& n = atom[0].getConst<Rational>();
        Node negated_n = nm->mkConst(-n); 
        return nm->mkNode(kind::LEQ, negated_diff, negated_n);
      }
      else // neither side is a difference, assume we are dealing with the case of (<= (x y))
      {
        // (x <= y) -> (x - y <= 0) 
        Node diff = nm->mkNode(kind::MINUS, atom[0], atom[1]);
        Node n = nm->mkConst(Rational(0));
        return nm->mkNode(kind::LEQ, diff, n);
      }
    }
    case kind::GT:
    {
      if(atom[0].getKind() == kind::MINUS) 
      {
        Node negated_diff = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
        const Rational& n = atom[1].getConst<Rational>();
        Node negated_n_minus1 = nm->mkConst(- n - Rational(1)); 
        return nm->mkNode(kind::LEQ, negated_diff, negated_n_minus1);
      }
      else if(atom[1].getKind() == kind::MINUS) 
      {
        // n > x - y  ->  x - y < n  ->  x -  y <= n - 1
        Node n_minus_1 = nm->mkConst(atom[0].getConst<Rational>() - Rational(1));
        return nm->mkNode(kind::LEQ, atom[1], n_minus_1);
      }
      else // neither side is a difference, assume we are dealing with the case of (> (x y))
      {
        // x > y  ->  0 > y - x  ->  y - x < 0  ->  y - x <= -1
        Node negated_diff = nm->mkNode(kind::MINUS, atom[1], atom[0]);
        Node n = nm->mkConst(Rational(-1));
        return nm->mkNode(kind::LEQ, negated_diff, n);
      }
    }
    case kind::GEQ:
    {
      if(atom[0].getKind() == kind::MINUS)
      {
        // x - y >= n  ->  -n >= y - x  ->  y - x <= -n
        Node negated_diff = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
        const Rational& n = atom[1].getConst<Rational>();
        Node negated_n = nm->mkConst(- n); 
        return nm->mkNode(kind::LEQ, negated_diff, negated_n);
      }
      else if(atom[1].getKind() == kind::MINUS)
      {
        return nm->mkNode(kind::LEQ, atom[1], atom[0]);
      }
      else // neither side is a difference, assume we are dealing with the case of (>= (x y))
      {
        // x >= y  ->  0 >= y - x  ->  y - x <= 0 
        Node negated_diff = nm->mkNode(kind::MINUS, atom[1], atom[0]);
        Node n = nm->mkConst(Rational(0));
        return nm->mkNode(kind::LEQ, negated_diff, n);
      }
    }
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
  //  cout << d_numVars << endl;
  //  cout << distance[0] << endl;
  //  cout << distance[1] << endl;
  //  cout << distance[2] << endl;
  //  cout << distance[3] << endl;
  // ---------------------------------------------------------------------------
  // TODO: implement model generation by computing the single-source shortest
  // path from a node that has distance zero to all other nodes
  // ---------------------------------------------------------------------------
    // Ford-Bellman, "relax" edges at least |V| - 1 times
    // (no cycles so it shouldn't matter if we do it more than |V| - 1 times!)
  for (int i = 0; i <= d_numVars; ++i)
  {
    for (int v1 = 0; v1 <= d_numVars - 1; ++v1)
    {
      for (int v2 = 0; v2 <= d_numVars - 1; ++v2)
      {
        if (d_valid[v1][v2])
        {
          Rational w = d_matrix[v1][v2];
          if (distance[v1] + w < distance[v2])
          {
            distance[v2] = distance[v1] + w;
          }
        }
      }
    }
  }

  // negate distances as per piazza post #30
  for (size_t i = 0; i < d_numVars; i++)
  {
    distance[i] = -distance[i];
  }

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
  // Code to detect a negative cycle.
  // Simple implementation of Bellman-Ford algorithm
  // adopted from wikipedia pseudo-code: https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm#Finding_negative_cycles
  // --------------------------------------------------------------------------
  Rational distance[d_numVars];
  distance[0] = 0;
  for (int v = 1; v <= d_numVars - 1; ++v)
  {
    // set the distance to "infinity" 9,999,999
    // note: this may not produce correct behavior if the sum
    // of weights for a cycle could possibly approach 9999999
    distance[v] =  9999999;
  }
  // measure distance from vertex 0 ("source")

  // Next, "relax" edges |V| - 1 times
  for (int i = 0; i <= d_numVars - 2; ++i)
  {
    for (int v1 = 0; v1 <= d_numVars - 1; ++v1)
    {
      for (int v2 = 0; v2 <= d_numVars - 1; ++v2)
      {
        if (d_valid[v1][v2])
        {
          Rational w = d_matrix[v1][v2];
          if (distance[v1] + w < distance[v2])
          {
            distance[v2] = distance[v1] + w;
          }
        }
      }
    }
  }

  // Check for negative weight cycles by trying to "relax" 
  // edges once more
  for (int v1 = 0; v1 <= d_numVars - 1; ++v1)
    {
      for (int v2 = 0; v2 <= d_numVars - 1; ++v2)
      {
        if (d_valid[v1][v2])
        {
          Rational w = d_matrix[v1][v2];
          if (distance[v1] + w < distance[v2])
          {
            // Then the graph contains a negative cycle
            return true;
          }
        }
      }
    }

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
