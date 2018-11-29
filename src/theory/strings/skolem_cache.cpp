/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a cache of skolems for theory of strings.
 **/

#include "theory/strings/skolem_cache.h"

#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "util/rational.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

SkolemCache::SkolemCache()
{
  NodeManager* nm = NodeManager::currentNM();
  d_strType = nm->stringType();
  d_zero = nm->mkConst(Rational(0));
}

Node SkolemCache::mkSkolemCached(Node a, Node b, SkolemId id, const char* c)
{
  return mkTypedSkolemCached(d_strType, a, b, id, c);
}

Node SkolemCache::mkSkolemCached(Node a, SkolemId id, const char* c)
{
  return mkSkolemCached(a, Node::null(), id, c);
}

Node SkolemCache::mkTypedSkolemCached(
    TypeNode tn, Node a, Node b, SkolemId id, const char* c)
{
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  if (tn == d_strType)
  {
    std::tie(id, a, b) = normalizeStringSkolem(id, a, b);
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    Node sk = mkTypedSkolem(tn, c);
    d_skolemCache[a][b][id] = sk;
    return sk;
  }
  return it->second;
}
Node SkolemCache::mkTypedSkolemCached(TypeNode tn,
                                      Node a,
                                      SkolemId id,
                                      const char* c)
{
  return mkTypedSkolemCached(tn, a, Node::null(), id, c);
}

Node SkolemCache::mkSkolem(const char* c)
{
  return mkTypedSkolem(d_strType, c);
}

Node SkolemCache::mkTypedSkolem(TypeNode tn, const char* c)
{
  Node n = NodeManager::currentNM()->mkSkolem(c, tn, "string skolem");
  d_allSkolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_allSkolems.find(n) != d_allSkolems.end();
}

std::tuple<SkolemCache::SkolemId, Node, Node>
SkolemCache::normalizeStringSkolem(SkolemId id, Node a, Node b)
{
  Trace("skolem-cache") << "normalizeStringSkolem start: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  if (id == SK_PURIFY && a.getKind() == kind::STRING_SUBSTR)
  {
    Node s = a[0];
    Node n = a[1];
    Node m = a[2];

    if (m.getKind() == kind::STRING_STRIDOF && m[0] == s && n == d_zero
        && m[2] == d_zero)
    {
      // SK_PURIFY(str.substr x 0 (str.indexof x y 0)) ---> SK_FIRST_CTN_PRE(x,
      // y)
      id = SK_FIRST_CTN_PRE;
      a = m[0];
      b = m[1];
    }
    else if (n.isConst() && m.getKind() == kind::PLUS
             && m.getNumChildren() == 2)
    {
      size_t ci = m[0].isConst() ? 0 : 1;
      Node c = m[ci];
      Node nc = m[1 - ci];

      if (c.isConst())
      {
        Rational cr = c.getConst<Rational>();
        Rational nr = n.getConst<Rational>();
        if (cr == nr * Rational(-1) && nr.sgn() > 0
            && nc.getKind() == kind::STRING_STRIDOF && nc[0] == s)
        {
          id = SK_FIRST_CTN_PRE;
          a = Rewriter::rewrite(
              nm->mkNode(STRING_SUBSTR,
                         s,
                         n,
                         nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, s), n)));
          b = nc[1];
        }
      }
    }
    else if (n.getKind() == kind::PLUS && n.getNumChildren() == 2)
    {
      // SK_PURIFY(str.substr x (+ (str.indexof x y 0) (str.len y)) n) --->
      // SK_FIRST_CTN_POST(x, y) if (+ (str.indexof x y 0) (str.len y) n) >=
      // (str.len x)
      size_t ci = n[0].isConst() ? 0 : 1;
      Node c = n[ci];
      Node nc = n[1 - ci];
      if (c.isConst() && nc.getKind() == kind::STRING_STRIDOF && nc[0] == s
          && nc[2] == d_zero)
      {
        Node sublen = nm->mkNode(STRING_LENGTH, nc[1]);
        Node len = nm->mkNode(STRING_LENGTH, s);
        Node end = nm->mkNode(PLUS, n, m);
        if (TheoryStringsRewriter::checkEntailArithEq(sublen, c)
            && TheoryStringsRewriter::checkEntailArith(end, len))
        {
          id = SK_FIRST_CTN_POST;
          a = s;
          b = nc[1];
        }
      }
    }
  }

  if (id == SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE((str.substr x 0 n), y) ---> SK_FIRST_CTN_PRE(x, y)
    while (a.getKind() == kind::STRING_SUBSTR && a[1] == d_zero)
    {
      a = a[0];
    }
  }

  if (id == SK_PREFIX)
  {
    // SK_PREFIX(x, (str.indexof x y 0)) ---> SK_FIRST_CTN_PRE(x, y)
    if (b.getKind() == kind::STRING_STRIDOF && b[0] == a && b[2] == d_zero)
    {
      id = SK_FIRST_CTN_PRE;
      b = b[1];
    }
  }

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
