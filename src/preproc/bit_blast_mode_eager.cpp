/*********************                                                        */
/*! \file bit_blast_mode_eager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A preprocessing pass that adds eager atoms .
 **
 ** A preprocessing pass that adds eager atoms
 **/

#include "preproc/bit_blast_mode_eager.h"

namespace CVC4 {
namespace preproc {

AddEagerAtomsPass::AddEagerAtomsPass(PreprocessingPassRegistry* registry)
    : PreprocessingPass(registry, "addEagerAtoms", true) {}

PreprocessingPassResult AddEagerAtomsPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
  d_theoryEngine = d_api->getTheoryEngine();
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    TNode atom = (*assertionsToPreprocess)[i];
    Node eager_atom =
        NodeManager::currentNM()->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
    assertionsToPreprocess->replace(i, eager_atom);
    theory::TheoryModel* m = d_theoryEngine->getModel();
    m->addSubstitution(eager_atom, atom);
  }
  return NO_CONFLICT;
}

}  // namespace preproc
}  // namespace CVC4
