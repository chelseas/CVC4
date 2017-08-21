/*********************                                                        */
/*! \file quantifiers_proof.cpp
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

#include "proof/quantifiers_proof.h"

#include "expr/node_manager.h"
#include "theory/quantifiers/instantiate.h"

namespace CVC4 {

Node QuantifiersProof::flattenQuantifier(Node term) const
{
  Assert(term.getKind() == kind::FORALL);

  NodeManager* nm = NodeManager::currentNM();
  Node body = term[1];
  for (size_t i = 0, size = term[0].getNumChildren(); i < size; i++)
  {
    Node variable = term[0][size - i - 1];
    body = nm->mkNode(
        kind::FORALL, nm->mkNode(kind::BOUND_VAR_LIST, variable), body);
  }
  return body;
}

void QuantifiersProof::registerTerm(Expr term)
{
  // recursively declare all other terms
  for (size_t i = 0, size = term.getNumChildren(); i < size; ++i)
  {
    // could belong to other theories
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCQuantifiersProof::printOwnedTerm(Expr term,
                                          std::ostream& os,
                                          const ProofLetMap& map)
{
  Assert(theory::Theory::theoryOf(term) == theory::THEORY_QUANTIFIERS);
  switch (term.getKind())
  {
    case kind::FORALL:
    {
      Assert(term[0].getKind() == kind::BOUND_VAR_LIST);
      std::ostringstream parens;
      for (size_t i = 0; i < term[0].getNumChildren(); i++)
      {
        os << "(forall _ ";
        d_proofEngine->printBoundTerm(term[0][i], os, map);
        os << " ";
        parens << ")";
      }
      d_proofEngine->printBoundTerm(term[1], os, map);
      os << parens.str();
      return;
    }
    default: { Unreachable(); }
  }
}

void LFSCQuantifiersProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                                 std::ostream& os,
                                                 std::ostream& paren,
                                                 const ProofLetMap& map)
{
  std::vector<Node> node_lemmas;
  for (const Expr& expr : lemma)
  {
    if (expr.getKind() == kind::NOT && expr[0].getKind() == kind::FORALL)
    {
      node_lemmas.push_back(Node::fromExpr(expr));
    }
  }

  std::map<Node, Node> quant;
  std::map<Node, std::vector<Node> > tvec;
  d_theoryQuantifiers->getQuantifiersEngine()->getExplanationForInstLemmas(
      node_lemmas, quant, tvec);

  for (const Node& node : node_lemmas)
  {
    Assert(node.getKind() == kind::NOT && node[0].getKind() == kind::FORALL);
    Node flattenedQuantifier = flattenQuantifier(node[0]);

    std::ostringstream parens;
    const std::vector<Node>& terms = tvec[node];
    for (size_t i = 0, size = terms.size(); i < size; i++)
    {
      Node term = terms[i];
      os << "(inst _ _ _ ";
      d_proofEngine->printBoundTerm(term.toExpr(), os, map);
      os << " ";

      Node var = flattenedQuantifier[0][0];
      flattenedQuantifier = flattenedQuantifier[1];
      std::vector<std::pair<Node, Node> > subst = {{var, term}};
      flattenedQuantifier =
          flattenedQuantifier.substitute(subst.begin(), subst.end());

      d_proofEngine->printBoundTerm(flattenedQuantifier.toExpr(), os, map);
      os << " ";

      if (i == 0)
      {
        os << ProofManager::getPreprocessedAssertionName(node[0]) << " ";
      }
      else
      {
        os << "t" << (i - 1) << " ";
      }

      os << "(\\ t" << i << " ";
      parens << "))";
    }

    // TODO: replace with a real proof that shows why the instantiation makes
    // the body false.
    os << "(clausify_false (trust_f false))";
    os << parens.str();
  }
}

}  // namespace CVC4
