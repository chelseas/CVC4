
#include "cvc4_private.h"

#pragma once

#include "proof/rewrite_proof_dispatcher.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

enum arrays_pre_Rewrites {
  arrays_pre_SELECT_STORE_I_I = LAST_SHARED,
  arrays_pre_SELECT_STORE_DIFF_CONSTS,
  arrays_pre_SELECT_STORE_DIFF_I_J,
  arrays_pre_SELECT_STORE_I_J,
  arrays_pre_SELECT_STORE_ALL,
  arrays_pre_STORE_SELECT,
  arrays_pre_STORE_STORE_I_I,
  arrays_pre_STORE_STORE_I_J,
  arrays_pre_X_EQ_X,
  arrays_pre_NORMALIZE_STORES,
  arrays_pre_CONST_X_EQ_CONST_Y,
  arrays_pre_NORM_X_EQ_Y
};

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite1(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite2(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::STORE) &&
      ((node[0]).getKind() == kind::STORE)) {
    if ((true) && (node[0][1] == node[1])) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_STORE_STORE_I_I);
      };
      Node rewritten_node =
          nm->mkNode(kind::STORE, node[0][0], node[0][1], node[2]);
      return arrays_pre_rewrite1<Proof>(rewritten_node, proof);
    };
    if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
        nm->mkConst(true)) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_STORE_STORE_I_J);
      };
      Node rewritten_node =
          nm->mkNode(kind::STORE, node[0][0], node[1], node[2]);
      return arrays_pre_rewrite1<Proof>(rewritten_node, proof);
    }
  };
  if (((node).getKind() == kind::EQUAL) && (true) && (node[0] == node[1])) {
    if (Proof) {
      proof->registerRewrite(arrays_pre_X_EQ_X);
    };
    Node rewritten_node = nm->mkConst(true);
    return arrays_pre_rewrite1<Proof>(rewritten_node, proof);
  };
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite3(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite4(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::STORE) &&
      ((node[2]).getKind() == kind::SELECT) && (true) &&
      (node[0] == node[2][0]) && (node[1] == node[2][1])) {
    if (Proof) {
      proof->registerRewrite(arrays_pre_STORE_SELECT);
    };
    Node rewritten_node = node[0];
    return arrays_pre_rewrite3<Proof>(rewritten_node, proof);
  };
  return arrays_pre_rewrite2<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite5(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite6(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::SELECT) &&
      ((node[0]).getKind() == kind::STORE_ALL) && (true)) {
    if (Proof) {
      proof->registerRewrite(arrays_pre_SELECT_STORE_ALL);
    };
    Node rewritten_node = node[0][0];
    return arrays_pre_rewrite5<Proof>(rewritten_node, proof);
  };
  return arrays_pre_rewrite4<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite7(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse arrays_pre_rewrite8(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::SELECT) &&
      ((node[0]).getKind() == kind::STORE)) {
    if ((true) && (node[0][1] == node[1])) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_SELECT_STORE_I_I);
      };
      Node rewritten_node = node[0][2];
      return arrays_pre_rewrite7<Proof>(rewritten_node, proof);
    };
    if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
        nm->mkConst(false)) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_SELECT_STORE_DIFF_I_J);
      };
      Node rewritten_node = nm->mkNode(kind::SELECT, node[0][0], node[1]);
      return arrays_pre_rewrite7<Proof>(rewritten_node, proof);
    };
    if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
        nm->mkConst(true)) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_SELECT_STORE_I_J);
      };
      Node rewritten_node = node[0][2];
      return arrays_pre_rewrite7<Proof>(rewritten_node, proof);
    };
    if ((((node[0][1]).isConst()) && ((node[1]).isConst())) &&
        ((node[0][1] != node[1]))) {
      if (Proof) {
        proof->registerRewrite(arrays_pre_SELECT_STORE_DIFF_CONSTS);
      };
      Node rewritten_node = nm->mkNode(kind::SELECT, node[0][0], node[1]);
      return arrays_pre_rewrite7<Proof>(rewritten_node, proof);
    }
  };
  return arrays_pre_rewrite6<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_pre_applyRules(TNode node, RewriteProof *proof) {

  return arrays_pre_rewrite8<Proof>(node, proof);
}

inline void arrays_pre_printProof(bool use_cache, TheoryProofEngine *tp,
                                  const Rewrite *rewrite, std::ostream &os,
                                  ProofLetMap &globalLetMap) {

  if (rewrite->d_tag == arrays_pre_SELECT_STORE_I_I) {
    os << "(select_store_i_i _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_SELECT_STORE_DIFF_CONSTS) {
    os << "(select_store_diff_consts _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_SELECT_STORE_DIFF_I_J) {
    os << "(select_store_diff_i_j _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_SELECT_STORE_I_J) {
    os << "(select_store_i_j _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_SELECT_STORE_ALL) {
    os << "(select_store_all _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_STORE_SELECT) {
    os << "(store_select _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_STORE_STORE_I_I) {
    os << "(store_store_i_i _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_STORE_STORE_I_J) {
    os << "(store_store_i_j _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_X_EQ_X) {
    os << "(x_eq_x _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_NORMALIZE_STORES) {
    os << "(normalize_stores _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_CONST_X_EQ_CONST_Y) {
    os << "(const_x_eq_const_y _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_pre_NORM_X_EQ_Y) {
    os << "(norm_x_eq_y _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  }
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
