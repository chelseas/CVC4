/*********************                                                        */
/*! \file theory_idl.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Mathias Preiner, Tim King
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

#pragma once

#include "cvc4_private.h"

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class TheoryIdl : public Theory {
 public:
  /** Theory constructor. */
  TheoryIdl(context::Context* c, context::UserContext* u, OutputChannel& out,
            Valuation valuation, const LogicInfo& logicInfo);

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode) override;

  /** Set up the solving data structures */
  void presolve() override;

  /** Clean up the solving data structures */
  void postsolve() override;

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom) override;

  /** Check the assertions for satisfiability */
  void check(Effort effort) override;

  /** Identity string */
  std::string identify() const override { return "THEORY_IDL"; }

  bool collectModelInfo(TheoryModel* m) override;

 private:
  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Return true iff the graph has a negative cycle */
  bool negativeCycle();

  /** Print the matrix */
  void printMatrix(const std::vector<std::vector<Rational>>& matrix, const std::vector<std::vector<bool>>& valid);

  typedef context::CDHashMap<TNode, size_t, TNodeHashFunction>
      TNodeToUnsignedCDMap;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /** i,jth entry is true iff there is an edge from i to j. */
  std::vector<std::vector<bool>> d_valid;

  /** i,jth entry stores weight for edge from i to j. */
  std::vector<std::vector<Rational>> d_matrix;

  /** Number of variables in the graph */
  size_t d_numVars;
};/* class TheoryIdl */

}/* CVC4::theory::idl namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
