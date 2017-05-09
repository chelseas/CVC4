
#include "cvc4_private.h"

#pragma once

#include "proof/rewrite_proof_dispatcher.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

enum arrays_post_Rewrites {
  arrays_post_SELECT_STORE_I_I = LAST_SHARED,
  arrays_post_SELECT_STORE_DIFF_CONSTS,
  arrays_post_SELECT_STORE_DIFF_I_J,
  arrays_post_SELECT_STORE_I_J,
  arrays_post_SELECT_STORE_ALL,
  arrays_post_STORE_SELECT,
  arrays_post_STORE_STORE_I_I,
  arrays_post_STORE_STORE_I_J,
  arrays_post_X_EQ_X,
  arrays_post_NORMALIZE_STORES,
  arrays_post_CONST_X_EQ_CONST_Y,
  arrays_post_NORM_X_EQ_Y
};

template <bool Proof>
inline RewriteResponse arrays_post_rewrite1(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite2(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::EQUAL) {
    if ((true) && (node[0] == node[1])) {
      if (Proof) {
        proof->registerRewrite(arrays_post_X_EQ_X);
      };
      Node rewritten_node = nm->mkConst(true);
      return arrays_post_rewrite1<Proof>(rewritten_node, proof);
    };
    if ((((node[0]).isConst()) && ((node[1]).isConst())) &&
        ((node[0] != node[1]))) {
      if (Proof) {
        proof->registerRewrite(arrays_post_CONST_X_EQ_CONST_Y);
      };
      Node rewritten_node = nm->mkConst(false);
      return arrays_post_rewrite1<Proof>(rewritten_node, proof);
    };
    if ((node[0]) > (node[1])) {
      if (Proof) {
        proof->registerRewrite(arrays_post_NORM_X_EQ_Y);
      };
      Node rewritten_node = nm->mkNode(kind::EQUAL, node[1], node[0]);
      return arrays_post_rewrite1<Proof>(rewritten_node, proof);
    }
  };
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite3(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN_FULL, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite4(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::STORE) &&
      ((node[0]).getKind() == kind::STORE) &&
      ((Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
        nm->mkConst(false)) &&
       ((node[0][1]) > (node[1])))) {
    if (Proof) {
      proof->registerRewrite(arrays_post_NORMALIZE_STORES);
    };
    Node rewritten_node = nm->mkNode(
        kind::STORE, nm->mkNode(kind::STORE, node[0][0], node[1], node[2]),
        node[0][1], node[0][2]);
    return arrays_post_rewrite3<Proof>(rewritten_node, proof);
  };
  return arrays_post_rewrite2<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite5(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite6(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::STORE) {
    if (((node[2]).getKind() == kind::SELECT) && (true) &&
        (node[0] == node[2][0]) && (node[1] == node[2][1])) {
      if (Proof) {
        proof->registerRewrite(arrays_post_STORE_SELECT);
      };
      Node rewritten_node = node[0];
      return arrays_post_rewrite5<Proof>(rewritten_node, proof);
    };
    if ((node[0]).getKind() == kind::STORE) {
      if ((true) && (node[0][1] == node[1])) {
        if (Proof) {
          proof->registerRewrite(arrays_post_STORE_STORE_I_I);
        };
        Node rewritten_node =
            nm->mkNode(kind::STORE, node[0][0], node[0][1], node[2]);
        return arrays_post_rewrite5<Proof>(rewritten_node, proof);
      };
      if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
          nm->mkConst(true)) {
        if (Proof) {
          proof->registerRewrite(arrays_post_STORE_STORE_I_J);
        };
        Node rewritten_node =
            nm->mkNode(kind::STORE, node[0][0], node[1], node[2]);
        return arrays_post_rewrite5<Proof>(rewritten_node, proof);
      }
    }
  };
  return arrays_post_rewrite4<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite7(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite8(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::SELECT) &&
      ((node[0]).getKind() == kind::STORE)) {
    if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
        nm->mkConst(false)) {
      if (Proof) {
        proof->registerRewrite(arrays_post_SELECT_STORE_DIFF_I_J);
      };
      Node rewritten_node = nm->mkNode(kind::SELECT, node[0][0], node[1]);
      return arrays_post_rewrite7<Proof>(rewritten_node, proof);
    };
    if ((((node[0][1]).isConst()) && ((node[1]).isConst())) &&
        ((node[0][1] != node[1]))) {
      if (Proof) {
        proof->registerRewrite(arrays_post_SELECT_STORE_DIFF_CONSTS);
      };
      Node rewritten_node = nm->mkNode(kind::SELECT, node[0][0], node[1]);
      return arrays_post_rewrite7<Proof>(rewritten_node, proof);
    }
  };
  return arrays_post_rewrite6<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite9(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse arrays_post_rewrite10(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::SELECT) {
    if ((node[0]).getKind() == kind::STORE) {
      if ((true) && (node[0][1] == node[1])) {
        if (Proof) {
          proof->registerRewrite(arrays_post_SELECT_STORE_I_I);
        };
        Node rewritten_node = node[0][2];
        return arrays_post_rewrite9<Proof>(rewritten_node, proof);
      };
      if (Rewriter::rewrite(nm->mkNode(kind::EQUAL, node[0][1], node[1])) ==
          nm->mkConst(true)) {
        if (Proof) {
          proof->registerRewrite(arrays_post_SELECT_STORE_I_J);
        };
        Node rewritten_node = node[0][2];
        return arrays_post_rewrite9<Proof>(rewritten_node, proof);
      }
    };
    if (((node[0]).getKind() == kind::STORE_ALL) && (true)) {
      if (Proof) {
        proof->registerRewrite(arrays_post_SELECT_STORE_ALL);
      };
      Node rewritten_node = node[0][0];
      return arrays_post_rewrite9<Proof>(rewritten_node, proof);
    }
  };
  return arrays_post_rewrite8<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse arrays_post_applyRules(TNode node, RewriteProof *proof) {

  return arrays_post_rewrite10<Proof>(node, proof);
}

inline void arrays_post_printProof(bool use_cache, TheoryProofEngine *tp,
                                   const Rewrite *rewrite, std::ostream &os,
                                   ProofLetMap &globalLetMap) {

  if (rewrite->d_tag == arrays_post_SELECT_STORE_I_I) {
    os << "(select_store_i_i _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_SELECT_STORE_DIFF_CONSTS) {
    os << "(select_store_diff_consts _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_SELECT_STORE_DIFF_I_J) {
    os << "(select_store_diff_i_j _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_SELECT_STORE_I_J) {
    os << "(select_store_i_j _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_SELECT_STORE_ALL) {
    os << "(select_store_all _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_STORE_SELECT) {
    os << "(store_select _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_STORE_STORE_I_I) {
    os << "(store_store_i_i _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_STORE_STORE_I_J) {
    os << "(store_store_i_j _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_X_EQ_X) {
    os << "(x_eq_x _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_NORMALIZE_STORES) {
    os << "(normalize_stores _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_CONST_X_EQ_CONST_Y) {
    os << "(const_x_eq_const_y _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == arrays_post_NORM_X_EQ_Y) {
    os << "(norm_x_eq_y _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  }
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
