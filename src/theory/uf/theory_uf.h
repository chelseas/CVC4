/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__THEORY_UF_H
#define CVC4__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace uf {

class CardinalityExtension;

class TheoryUF : public Theory
{
 public:
  /** Theory constructor. */
  TheoryUF(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo);

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
  std::string identify() const override { return "THEORY_UF"; }

  bool collectModelInfo(TheoryModel* m) override;

  CardinalityExtension* getCardinalityExtension() const
  {
    // Not implemented for the lab
    Unimplemented();
  }

  bool inConflict() const { Unimplemented(); }
}; /* class TheoryUF */

}  // namespace uf
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__UF__THEORY_UF_H */
