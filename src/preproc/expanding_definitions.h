/*********************                                                        */
/*! \file expanding_definitions.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for expanding definitions pass
 **
 ** Implementation for expanding definitions pass..
 **/
#include "cvc4_private.h"
#ifndef __CVC4__PREPROC__EXPANDING_DEFINITIONS_H
#define __CVC4__PREPROC__EXPANDING_DEFINITIONS_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;

class ExpandingDefinitionsPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess);
  ExpandingDefinitionsPass(PreprocessingPassRegistry* registry);

 private:
  SmtEngine* d_smt;
  TheoryEngine* d_theoryEngine;
  Node expandDefinitions(
      TNode n, NodeToNodeHashMap& cache,
      bool expandOnly = false) throw(TypeCheckingException, LogicException,
                                     UnsafeInterruptException);
};

}  // preproc namespace
}  // CVC4 namespace

#endif /* __CVC4__PREPROC__EXPANDING_DEFINITIONS_H */
