/*********************                                                        */
/*! \file theory_arrays_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

Node getMostFrequentValue(TNode store);
uint64_t getMostFrequentValueCount(TNode store);
void setMostFrequentValue(TNode store, TNode value);
void setMostFrequentValueCount(TNode store, uint64_t count);

static inline Node mkEqNode(Node a, Node b) {
  return a.getType().isBoolean() ? a.iffNode(b) : a.eqNode(b);
}

class TheoryArraysRewriter {
 private:
  static Node normalizeConstant(TNode node) {
    return normalizeConstant(node, node[1].getType().getCardinality());
  }

 public:
  // this function is called by printers when using the option
  // "--model-u-dt-enum"
  static Node normalizeConstant(TNode node, Cardinality indexCard);

  static RewriteResponse postRewrite(TNode node);
  static RewriteResponse preRewrite(TNode node);

  static inline void init() {}
  static inline void shutdown() {}

}; /* class TheoryArraysRewriter */

} /* CVC4::theory::arrays namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
