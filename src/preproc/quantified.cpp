/*********************                                                        */
/*! \file quantified.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that processes quantified passes.
 **
 ** Preprocessing pass that processes quantified passes and the fmf fun well
 *defined flag.
 **/
#include "preproc/quantified.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/macros.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_rewriter.h"

namespace CVC4 {
namespace preproc {

QuantifiedPass::QuantifiedPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "quantified", true) {}

PreprocessingPassResult QuantifiedPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  d_smt = d_api->getSmt();
  d_fmfRecFunctionsAbs = d_api->getFmfRecFunctionsAbs();
  d_fmfRecFunctionsConcrete = d_api->getFmfRecFunctionsConcrete();
  d_fmfRecFunctionsDefined = d_api->getFmfRecFunctionsDefined();
  // remove rewrite rules, apply pre-skolemization to existential quantifiers
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    Node prev = (*assertionsToPreprocess)[i];
    Node next = theory::quantifiers::QuantifiersRewriter::preprocess(prev);
    if (next != prev) {
      assertionsToPreprocess->replace(i, theory::Rewriter::rewrite(next));
      Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev
                                      << std::endl;
      Trace("quantifiers-preprocess")
          << "   ...got " << (*assertionsToPreprocess)[i] << std::endl;
    }
  }
  if (options::macrosQuant()) {
    // quantifiers macro expansion
    theory::quantifiers::QuantifierMacros qm(
        d_theoryEngine->getQuantifiersEngine());
    bool success;
    do {
      success = qm.simplify(assertionsToPreprocess->ref(), true);
    } while (success);
    // finalize the definitions
    qm.finalizeDefinitions();
  }

  // fmf-fun : assume admissible functions, applying preprocessing reduction to
  // FMF
  if (options::fmfFunWellDefined()) {
    theory::quantifiers::FunDefFmf fdf;
    Assert(d_fmfRecFunctionsDefined != NULL);
    // must carry over current definitions (for incremental)
    for (context::CDList<Node>::const_iterator fit =
             d_fmfRecFunctionsDefined->begin();
         fit != d_fmfRecFunctionsDefined->end(); ++fit) {
      Node f = (*fit);
      Assert(d_fmfRecFunctionsAbs->find(f) != d_fmfRecFunctionsAbs->end());
      TypeNode ft = (*d_fmfRecFunctionsAbs)[f];
      fdf.d_sorts[f] = ft;
      std::map<Node, std::vector<Node> >::iterator fcit =
          d_fmfRecFunctionsConcrete->find(f);
      Assert(fcit != d_fmfRecFunctionsConcrete->end());
      for (unsigned j = 0; j < fcit->second.size(); j++) {
        fdf.d_input_arg_inj[f].push_back(fcit->second[j]);
      }
    }
    fdf.simplify(assertionsToPreprocess->ref());
    // must store new definitions (for incremental)
    for (unsigned i = 0; i < fdf.d_funcs.size(); i++) {
      Node f = fdf.d_funcs[i];
      (*d_fmfRecFunctionsAbs)[f] = fdf.d_sorts[f];
      (*d_fmfRecFunctionsConcrete)[f].clear();
      for (unsigned j = 0; j < fdf.d_input_arg_inj[f].size(); j++) {
        (*d_fmfRecFunctionsConcrete)[f].push_back(fdf.d_input_arg_inj[f][j]);
      }
      d_fmfRecFunctionsDefined->push_back(f);
    }
  }
  return NO_CONFLICT;
}
}  // namespace preproc
}  // namespace CVC4
