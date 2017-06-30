/*********************                                                        */
/*! \file rewrite_apply_to_const.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that applies rewrite to const
 **
 ** Preprocessing pass that applies rewrite to const.
 **/
#include "preproc/rewrite_apply_to_const.h"

namespace CVC4 {
namespace preproc {

RewriteApplyToConstPass::RewriteApplyToConstPass(
    PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "rewriteApplyToConst", true) {}

Node RewriteApplyToConstPass::rewriteApplyToConst(TNode n) {
  NodeToNodeHashMap d_rewriteApplyToConstCache;
  Trace("rewriteApplyToConst") << "rewriteApplyToConst :: " << n << std::endl;

  if (n.getMetaKind() == kind::metakind::CONSTANT ||
      n.getMetaKind() == kind::metakind::VARIABLE ||
      n.getMetaKind() == kind::metakind::NULLARY_OPERATOR) {
    return n;
  }

  if (d_rewriteApplyToConstCache.find(n) != d_rewriteApplyToConstCache.end()) {
    Trace("rewriteApplyToConst")
        << "in cache :: " << d_rewriteApplyToConstCache[n] << std::endl;
    return d_rewriteApplyToConstCache[n];
  }

  if (n.getKind() == kind::APPLY_UF) {
    if (n.getNumChildren() == 1 && n[0].isConst() &&
        n[0].getType().isInteger()) {
      std::stringstream ss;
      ss << n.getOperator() << "_";
      if (n[0].getConst<Rational>() < 0) {
        ss << "m" << -n[0].getConst<Rational>();
      } else {
        ss << n[0];
      }
      Node newvar = NodeManager::currentNM()->mkSkolem(
          ss.str(), n.getType(), "rewriteApplyToConst skolem",
          NodeManager::SKOLEM_EXACT_NAME);
      d_rewriteApplyToConstCache[n] = newvar;
      Trace("rewriteApplyToConst") << "made :: " << newvar << std::endl;
      return newvar;
    } else {
      std::stringstream ss;
      ss << "The rewrite-apply-to-const preprocessor is currently limited;"
         << std::endl
         << "it only works if all function symbols are unary and with Integer"
         << std::endl
         << "domain, and all applications are to integer values." << std::endl
         << "Found application: " << n;
      Unhandled(ss.str());
    }
  }
  NodeBuilder<> builder(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << n.getOperator();
  }
  for (unsigned i = 0; i < n.getNumChildren(); ++i) {
    builder << rewriteApplyToConst(n[i]);
  }
  Node rewr = builder;
  d_rewriteApplyToConstCache[n] = rewr;
  Trace("rewriteApplyToConst") << "built :: " << rewr << std::endl;
  return rewr;
}

PreprocessingPassResult RewriteApplyToConstPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    (*assertionsToPreprocess)[i] = theory::Rewriter::rewrite(
        rewriteApplyToConst((*assertionsToPreprocess)[i]));
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
