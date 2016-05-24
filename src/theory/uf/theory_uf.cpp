/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
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

#include "theory/uf/theory_uf.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {

TheoryUF::TheoryUF(context::Context* c,
                   context::UserContext* u,
                   OutputChannel& out,
                   Valuation valuation,
                   const LogicInfo& logicInfo)
    : Theory(THEORY_UF, c, u, out, valuation, logicInfo), d_em(&out)
{
}

void TheoryUF::preRegisterTerm(TNode node)
{
  // Nothing to do here
}

void TheoryUF::presolve()
{
  // Nothing to do here
}

void TheoryUF::postsolve()
{
  // Nothing to do here
}

Node TheoryUF::ppRewrite(TNode atom)
{
  // Nothing to do here
  return atom;
}

void TheoryUF::check(Effort level)
{
  if (!fullEffort(level))
  {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  bool conflict = false;

  std::vector<TNode> assertions;
  for (assertions_iterator i = facts_begin(); i != facts_end(); ++i)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would use `Theory::get()` to
    // only get new assertions.
    Assertion assertion = (*i);
    assertions.push_back(assertion.assertion);
  }

  // --------------------------------------------------------------------------
  // TODO: implement congruence closure.
  // --------------------------------------------------------------------------

  if (conflict)
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

bool TheoryUF::collectModelInfo(TheoryModel* m) { return true; }

}  // namespace uf
}  // namespace theory
} /* namespace CVC4 */
