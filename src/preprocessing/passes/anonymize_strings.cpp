/*********************                                                        */
/*! \file anonymize_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The rewrite preprocessing pass
 **
 ** Calls the rewriter on every assertion
 **/

#include "preprocessing/passes/anonymize_strings.h"

#include <unordered_map>
#include <unordered_set>

#include "options/strings_options.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

namespace {
void collectLits(Node n, std::unordered_map<Node, Node, NodeHashFunction>* lits)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = false;

      visit.push_back(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        visit.push_back(cur[i]);
      }
    }
    else if (!it->second)
    {
      if (cur.getKind() == kind::CONST_STRING)
      {
        if (lits->find(cur) == lits->end())
        {
          (*lits)[cur] = nm->mkSkolem("s", nm->stringType());
        }
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
}

std::unordered_map<Node, std::vector<Node>, NodeHashFunction>
computeContainsRels(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits)
{
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> containsRels;
  for (const auto& kv : lits)
  {
    // Make sure that each literal is a key
    containsRels[kv.second];
  }

  for (const auto& kv1 : lits)
  {
    for (const auto& kv2 : lits)
    {
      Node s1 = kv1.first;
      Node s2 = kv2.first;
      if (kv1.first != kv2.first)
      {
        if (s1.getConst<String>().find(s2.getConst<String>())
            != std::string::npos)
        {
          containsRels[kv1.second].push_back(kv2.second);
        }
      }
    }
  }
  return containsRels;
}

bool isNotCtn(
    Node t,
    Node s,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  std::vector<Node> toVisit = containsRels.at(t);
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    Assert(curr != t);
    if (curr == s)
    {
      return false;
    } else {
      toVisit.insert(toVisit.end(), containsRels.at(curr).begin(), containsRels.at(curr).end());
    }
  }

  return true;
}

void indirectContains(
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels,
    Node t,
    std::unordered_set<Node, NodeHashFunction>& res)
{
  res.insert(t);
  for(const Node& n : containsRels.at(t)) {
    indirectContains(containsRels, n, res);
  }
}

bool needNegCtn(
    Node t,
    Node s,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  /*return true;
  if (!containsRels.at(s).empty()) {
    std::cout << "Unnecessary neg ctn: " << s << " " << t << std::endl;
  }*/

  std::unordered_set<Node, NodeHashFunction> ic;
  indirectContains(containsRels, t, ic);

  for (const Node& n : containsRels.at(s)) {
    if (ic.find(n) != ic.end()) {
      return true;
    }
  }

  return containsRels.at(s).empty();
}

std::vector<Node> mkQueries(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> queries;

  std::unordered_map<Node, size_t, NodeHashFunction> lengths;
  unsigned i = 0;
  if (options::anonymizeStringsPreserveLengths())
  {
    for (const auto& kv : lits)
    {
      size_t length = kv.first.getConst<String>().size();
      lengths[kv.second] = length;
      queries.push_back(nm->mkNode(kind::EQUAL,
                                   nm->mkNode(kind::STRING_LENGTH, kv.second),
                                   nm->mkConst(Rational(length))));

      if (length == 1)
      {
        queries.push_back(
            nm->mkNode(kind::EQUAL,
                       kv.second,
                       nm->mkConst(String(std::vector<unsigned>{i}))));
        i++;
      }
    }
  }

  for (const auto& kv : containsRels)
  {
    for (const Node& containee : kv.second)
    {
      queries.push_back(nm->mkNode(kind::STRING_STRCTN, kv.first, containee));
    }
  }

  if (containsRels.size() > 1)
  {
    if (options::anonymizeStringsUseDistinct())
    {
      // Distinct strings constraints
      std::vector<Node> vars;
      for (const auto& kv : containsRels)
      {
        vars.push_back(kv.first);
      }
      queries.push_back(nm->mkNode(kind::DISTINCT, vars));
    }
    else
    {
      // Negative contains constraints
      for (const auto& kv1 : containsRels)
      {
        for (const auto& kv2 : containsRels)
        {
          if (kv1.first != kv2.first
              && isNotCtn(kv1.first, kv2.first, containsRels))
          {
            if (needNegCtn(kv1.first, kv2.first, containsRels))
            {
              if (!options::anonymizeStringsPreserveLengths()
                  || lengths[kv1.first] > lengths[kv2.first])
              {
                queries.push_back(nm->mkNode(
                    kind::NOT,
                    nm->mkNode(kind::STRING_STRCTN, kv1.first, kv2.first)));
              }
              else if (lengths[kv1.first] == lengths[kv2.first])
              {
                queries.push_back(nm->mkNode(
                    kind::NOT, nm->mkNode(kind::EQUAL, kv1.first, kv2.first)));
              }
            }
          }
        }
      }
    }
  }
  return queries;
}
}  // namespace

AnonymizeStrings::AnonymizeStrings(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "anonymize-strings"){};

PreprocessingPassResult AnonymizeStrings::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();

  std::unordered_map<Node, Node, NodeHashFunction> lits;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    collectLits((*assertionsToPreprocess)[i], &lits);
  }

  Trace("anonymize-strings") << "String literals: " << lits << std::endl;

  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> containsRels =
      computeContainsRels(lits);

  Trace("anonymize-strings")
      << "Contains relationships: " << containsRels << std::endl;

  std::vector<Node> queries = mkQueries(lits, containsRels);

  Trace("anonymize-strings") << "Queries: " << queries << std::endl;

  bool dumpBenchmark = Dump.on("benchmark");

  ExprManager em(nm->getOptions());
  SmtEngine checker(&em);

  {
    smt::SmtScope smts(&checker);
    Dump.off();
  }

  checker.setOption("anonymize-strings", false);
  checker.setOption("preprocess-only", false);
  checker.setOption("produce-models", true);

  ExprManagerMapCollection varMap;
  for (const Node& query : queries)
  {
    Expr equery = query.toExpr().exportTo(&em, varMap);
    checker.assertFormula(equery);
  }
  checker.checkSat();

  std::unordered_map<Node, Node, NodeHashFunction> substs;
  Trace("anonymize-strings") << "Values:" << std::endl;
  for (const auto& kv : lits)
  {
    Expr esk = kv.second.toExpr().exportTo(&em, varMap);
    substs[kv.first] = Node::fromExpr(checker.getValue(esk));
    Trace("anonymize-strings") << "..." << kv.second << " = " << kv.first
                               << " -> " << checker.getValue(esk) << std::endl;
  }

  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i,
                                    (*assertionsToPreprocess)[i].substitute(
                                        substs.begin(), substs.end(), cache));

    if (dumpBenchmark)
    {
      // HACK!!!!
      std::cout << "(assert " << (*assertionsToPreprocess)[i] << ")"
                << std::endl;
    }
  }

  if (dumpBenchmark)
  {
    // HACK!!!!
    std::cout << "(check-sat)" << std::endl;
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
