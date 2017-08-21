/*********************                                                        */
/*! \file quantifiers_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quantifiers proof
 **
 ** Quantifiers proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__QUANTIFIERS_PROOF_H
#define __CVC4__PROOF__QUANTIFIERS_PROOF_H

#include <map>

#include "expr/node.h"
#include "proof/theory_proof.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {

class QuantifiersProof : public TheoryProof
{
 protected:
  theory::quantifiers::TheoryQuantifiers* d_theoryQuantifiers;

 public:
  QuantifiersProof(theory::quantifiers::TheoryQuantifiers* theoryQuantifiers,
                   TheoryProofEngine* proofEngine)
      : TheoryProof(theoryQuantifiers, proofEngine),
        d_theoryQuantifiers(theoryQuantifiers)
  {
  }

  theory::TheoryId getTheoryId() override;

  Node flattenQuantifier(Node term) const;
  void registerTerm(Expr term) override;
};

class LFSCQuantifiersProof : public QuantifiersProof
{
 public:
  LFSCQuantifiersProof(
      theory::quantifiers::TheoryQuantifiers* theoryQuantifiers,
      TheoryProofEngine* proofEngine)
      : QuantifiersProof(theoryQuantifiers, proofEngine)
  {
  }

  void printOwnedTerm(Expr term,
                      std::ostream& os,
                      const ProofLetMap& map) override;
  void printOwnedSort(Type type, std::ostream& os) override {}
  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printSortDeclarations(std::ostream& os, std::ostream& paren) override {}
  void printTermDeclarations(std::ostream& os, std::ostream& paren) override {}

  void printDeferredDeclarations(std::ostream& os, std::ostream& paren) override
  {
  }

  void printAliasingDeclarations(std::ostream& os,
                                 std::ostream& paren,
                                 const ProofLetMap& globalLetMap) override
  {
  }
};

}  // namespace CVC4

#endif /* __CVC4__PROOF__QUANTIFIERS_PROOF_H */
