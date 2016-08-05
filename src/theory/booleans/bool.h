
#include "cvc4_private.h"

#pragma once

#include "proof/rewrite_proof_dispatcher.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

enum bool_Rewrites {
  NOT_TRUE = LAST_SHARED,
  NOT_FALSE,
  NOT_NOT,
  OR_TRUE,
  OR_FALSE,
  OR_DUP,
  AND_FALSE,
  AND_TRUE,
  AND_DUP,
  FALSE_IMPLIES,
  IMPLIES_TRUE,
  TRUE_IMPLIES_FALSE,
  TRUE_IMPLIES,
  IMPLIES_FALSE,
  TRUE_EQ,
  FALSE_EQ,
  X_EQ_X,
  N_X_EQ_X,
  EQ_EQ_CONSTS,
  EQ_NEQ_CONSTS_CARD2,
  EQ_NEQ_CONSTS,
  TRUE_XOR,
  FALSE_XOR,
  X_XOR_X,
  N_X_XOR_X,
  ITE_TRUE,
  ITE_FALSE,
  ITE_X_TRUE_FALSE,
  ITE_C_FALSE_TRUE,
  ITE_C_X_X,
  ITE_C_X_N_X,
  ITE_C_N_X_X,
  ITE_X_X_Y,
  ITE_N_X_X_Y,
  ITE_X_N_X_Y,
  ITE_X_Y_X,
  ITE_N_X_Y_X,
  ITE_X_Y_N_X,
  ITE_C_ITE_C_X_Y_Z,
  ITE_C_ITE_N_C_X_Y_Z,
  ITE_N_C_ITE_C_X_Y_Z,
  ITE_C_Z_ITE_C_X_Y,
  ITE_C_Z_ITE_N_C_X_Y,
  ITE_N_C_Z_ITE_C_X_Y
};

template <bool Proof>
inline RewriteResponse rewrite1(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite2(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::ITE) {
    if (((node[0]).getKind() == kind::CONST_BOOLEAN) && (true)) {
      if (node[0] == nm->mkConst(true)) {
        if (Proof) {
          proof->registerRewrite(ITE_TRUE);
        };
        Node rewritten_node = node[1];
        return rewrite1<Proof>(rewritten_node, proof);
      };
      if (node[0] == nm->mkConst(false)) {
        if (Proof) {
          proof->registerRewrite(ITE_FALSE);
        };
        Node rewritten_node = node[2];
        return rewrite1<Proof>(rewritten_node, proof);
      }
    };
    if (((node[1]).getKind() == kind::CONST_BOOLEAN) &&
        ((node[2]).getKind() == kind::CONST_BOOLEAN) && (true)) {
      if ((node[1] == nm->mkConst(true)) && (node[2] == nm->mkConst(false))) {
        if (Proof) {
          proof->registerRewrite(ITE_X_TRUE_FALSE);
        };
        Node rewritten_node = node[0];
        return rewrite1<Proof>(rewritten_node, proof);
      };
      if ((node[1] == nm->mkConst(false)) && (node[2] == nm->mkConst(true))) {
        if (Proof) {
          proof->registerRewrite(ITE_C_FALSE_TRUE);
        };
        Node rewritten_node = nm->mkNode(kind::NOT, node[0]);
        return rewrite1<Proof>(rewritten_node, proof);
      }
    };
    if ((true) && (node[1] == node[2])) {
      if (Proof) {
        proof->registerRewrite(ITE_C_X_X);
      };
      Node rewritten_node = node[1];
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[2]).getKind() == kind::NOT) && (true) &&
        (node[1] == node[2][0])) {
      if (Proof) {
        proof->registerRewrite(ITE_C_X_N_X);
      };
      Node rewritten_node = nm->mkNode(kind::EQUAL, node[0], node[1]);
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[1]).getKind() == kind::NOT) && (true) &&
        (node[1][0] == node[2])) {
      if (Proof) {
        proof->registerRewrite(ITE_C_N_X_X);
      };
      Node rewritten_node =
          nm->mkNode(kind::EQUAL, node[0], nm->mkNode(kind::NOT, node[1][0]));
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if ((!((node[0]).isConst())) && (node[0] == node[1])) {
      if (Proof) {
        proof->registerRewrite(ITE_X_X_Y);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0], nm->mkConst(true), node[2]);
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[0]).getKind() == kind::NOT) && (!((node[0][0]).isConst())) &&
        (node[0][0] == node[1])) {
      if (Proof) {
        proof->registerRewrite(ITE_N_X_X_Y);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, nm->mkNode(kind::NOT, node[0][0]),
                     nm->mkConst(false), node[2]);
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[1]).getKind() == kind::NOT) && (!((node[0]).isConst())) &&
        (node[0] == node[1][0])) {
      if (Proof) {
        proof->registerRewrite(ITE_X_N_X_Y);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0], nm->mkConst(false), node[2]);
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if ((!((node[0]).isConst())) && (node[0] == node[2])) {
      if (Proof) {
        proof->registerRewrite(ITE_X_Y_X);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0], node[1], nm->mkConst(false));
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[0]).getKind() == kind::NOT) && (!((node[0][0]).isConst())) &&
        (node[0][0] == node[2])) {
      if (Proof) {
        proof->registerRewrite(ITE_N_X_Y_X);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, nm->mkNode(kind::NOT, node[0][0]), node[1],
                     nm->mkConst(true));
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if (((node[2]).getKind() == kind::NOT) && (!((node[0]).isConst())) &&
        (node[0] == node[2][0])) {
      if (Proof) {
        proof->registerRewrite(ITE_X_Y_N_X);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0], node[1], nm->mkConst(true));
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if ((node[1]).getKind() == kind::ITE) {
      if ((true) && (node[0] == node[1][0])) {
        if (Proof) {
          proof->registerRewrite(ITE_C_ITE_C_X_Y_Z);
        };
        Node rewritten_node =
            nm->mkNode(kind::ITE, node[0], node[1][1], node[2]);
        return rewrite1<Proof>(rewritten_node, proof);
      };
      if (((node[1][0]).getKind() == kind::NOT) && (true) &&
          (node[0] == node[1][0][0])) {
        if (Proof) {
          proof->registerRewrite(ITE_C_ITE_N_C_X_Y_Z);
        };
        Node rewritten_node =
            nm->mkNode(kind::ITE, node[0], node[1][2], node[2]);
        return rewrite1<Proof>(rewritten_node, proof);
      }
    };
    if (((node[0]).getKind() == kind::NOT) &&
        ((node[1]).getKind() == kind::ITE) && (true) &&
        (node[0][0] == node[1][0])) {
      if (Proof) {
        proof->registerRewrite(ITE_N_C_ITE_C_X_Y_Z);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0][0], node[1][2], node[2]);
      return rewrite1<Proof>(rewritten_node, proof);
    };
    if ((node[2]).getKind() == kind::ITE) {
      if ((true) && (node[0] == node[2][0])) {
        if (Proof) {
          proof->registerRewrite(ITE_C_Z_ITE_C_X_Y);
        };
        Node rewritten_node =
            nm->mkNode(kind::ITE, node[0], node[1], node[2][2]);
        return rewrite1<Proof>(rewritten_node, proof);
      };
      if (((node[2][0]).getKind() == kind::NOT) && (true) &&
          (node[0] == node[2][0][0])) {
        if (Proof) {
          proof->registerRewrite(ITE_C_Z_ITE_N_C_X_Y);
        };
        Node rewritten_node =
            nm->mkNode(kind::ITE, node[0], node[1], node[2][1]);
        return rewrite1<Proof>(rewritten_node, proof);
      }
    };
    if (((node[0]).getKind() == kind::NOT) &&
        ((node[2]).getKind() == kind::ITE) && (true) &&
        (node[0][0] == node[2][0])) {
      if (Proof) {
        proof->registerRewrite(ITE_N_C_Z_ITE_C_X_Y);
      };
      Node rewritten_node =
          nm->mkNode(kind::ITE, node[0][0], node[1], node[2][1]);
      return rewrite1<Proof>(rewritten_node, proof);
    }
  };
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite3(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite4(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::XOR) && (true)) {
    for (unsigned in_tmp352 = 0, in_tmp352_end = node.getNumChildren();
         in_tmp352 < in_tmp352_end; in_tmp352++) {
      TNode n_tmp352 = node[in_tmp352];

      for (unsigned in_tmp351 = 0, in_tmp351_end = node.getNumChildren();
           in_tmp351 < in_tmp351_end; in_tmp351++) {
        TNode n_tmp351 = node[in_tmp351];
        if (!(in_tmp352 == in_tmp351)) {
          if (n_tmp351 == n_tmp352) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(X_XOR_X);
            };
            Node rewritten_node = nm->mkConst(false);
            return rewrite3<Proof>(rewritten_node, proof);
          };
          if (((n_tmp351).getKind() == kind::NOT) &&
              (n_tmp351[0] == n_tmp352)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(N_X_XOR_X);
            };
            Node rewritten_node = nm->mkConst(true);
            return rewrite3<Proof>(rewritten_node, proof);
          }
        }
      }
    }
  };
  return rewrite2<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite5(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite6(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::XOR) && (true)) {
    for (unsigned in_tmp348 = 0, in_tmp348_end = node.getNumChildren();
         in_tmp348 < in_tmp348_end; in_tmp348++) {
      TNode n_tmp348 = node[in_tmp348];

      for (unsigned in_tmp347 = 0, in_tmp347_end = node.getNumChildren();
           in_tmp347 < in_tmp347_end; in_tmp347++) {
        TNode n_tmp347 = node[in_tmp347];
        if ((!(in_tmp348 == in_tmp347)) &&
            ((n_tmp347).getKind() == kind::CONST_BOOLEAN)) {
          if (n_tmp347 == nm->mkConst(true)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(TRUE_XOR);
            };
            Node rewritten_node = nm->mkNode(kind::NOT, n_tmp348);
            return rewrite5<Proof>(rewritten_node, proof);
          };
          if (n_tmp347 == nm->mkConst(false)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(FALSE_XOR);
            };
            Node rewritten_node = n_tmp348;
            return rewrite5<Proof>(rewritten_node, proof);
          }
        }
      }
    }
  };
  return rewrite4<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite7(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN_FULL, node);
}

template <bool Proof>
inline RewriteResponse rewrite8(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::EQUAL) {
    for (unsigned in_tmp342 = 0, in_tmp342_end = node.getNumChildren();
         in_tmp342 < in_tmp342_end; in_tmp342++) {
      TNode n_tmp342 = node[in_tmp342];
      if ((n_tmp342).getKind() == kind::EQUAL) {
        for (unsigned in_tmp341 = 0, in_tmp341_end = node.getNumChildren();
             in_tmp341 < in_tmp341_end; in_tmp341++) {
          TNode n_tmp341 = node[in_tmp341];
          if ((!(in_tmp342 == in_tmp341)) &&
              ((n_tmp341).getKind() == kind::EQUAL)) {
            for (unsigned in_tmp346 = 0,
                          in_tmp346_end = n_tmp342.getNumChildren();
                 in_tmp346 < in_tmp346_end; in_tmp346++) {
              TNode n_tmp346 = n_tmp342[in_tmp346];

              for (unsigned in_tmp345 = 0,
                            in_tmp345_end = n_tmp342.getNumChildren();
                   in_tmp345 < in_tmp345_end; in_tmp345++) {
                TNode n_tmp345 = n_tmp342[in_tmp345];
                if (!(in_tmp346 == in_tmp345)) {
                  for (unsigned in_tmp344 = 0,
                                in_tmp344_end = n_tmp341.getNumChildren();
                       in_tmp344 < in_tmp344_end; in_tmp344++) {
                    TNode n_tmp344 = n_tmp341[in_tmp344];
                    if (n_tmp344 == n_tmp346) {
                      for (unsigned in_tmp343 = 0,
                                    in_tmp343_end = n_tmp341.getNumChildren();
                           in_tmp343 < in_tmp343_end; in_tmp343++) {
                        TNode n_tmp343 = n_tmp341[in_tmp343];
                        if ((!(in_tmp344 == in_tmp343)) &&
                            ((((n_tmp343).isConst()) &&
                              ((n_tmp345).isConst())) &&
                             ((n_tmp343 != n_tmp345)))) {
                          if (Proof) {
                            proof->registerSwap(0, 0);
                            proof->registerRewrite(EQ_NEQ_CONSTS);
                          };
                          Node rewritten_node = nm->mkNode(
                              kind::AND,
                              nm->mkNode(
                                  kind::NOT,
                                  nm->mkNode(kind::EQUAL, n_tmp343, n_tmp344)),
                              nm->mkNode(
                                  kind::NOT,
                                  nm->mkNode(kind::EQUAL, n_tmp345, n_tmp344)));
                          return rewrite7<Proof>(rewritten_node, proof);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };
  return rewrite6<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite9(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite10(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::EQUAL) {
    for (unsigned in_tmp330 = 0, in_tmp330_end = node.getNumChildren();
         in_tmp330 < in_tmp330_end; in_tmp330++) {
      TNode n_tmp330 = node[in_tmp330];
      if ((n_tmp330).getKind() == kind::EQUAL) {
        for (unsigned in_tmp329 = 0, in_tmp329_end = node.getNumChildren();
             in_tmp329 < in_tmp329_end; in_tmp329++) {
          TNode n_tmp329 = node[in_tmp329];
          if ((!(in_tmp330 == in_tmp329)) &&
              ((n_tmp329).getKind() == kind::EQUAL)) {
            for (unsigned in_tmp334 = 0,
                          in_tmp334_end = n_tmp330.getNumChildren();
                 in_tmp334 < in_tmp334_end; in_tmp334++) {
              TNode n_tmp334 = n_tmp330[in_tmp334];

              for (unsigned in_tmp333 = 0,
                            in_tmp333_end = n_tmp330.getNumChildren();
                   in_tmp333 < in_tmp333_end; in_tmp333++) {
                TNode n_tmp333 = n_tmp330[in_tmp333];
                if (!(in_tmp334 == in_tmp333)) {
                  for (unsigned in_tmp332 = 0,
                                in_tmp332_end = n_tmp329.getNumChildren();
                       in_tmp332 < in_tmp332_end; in_tmp332++) {
                    TNode n_tmp332 = n_tmp329[in_tmp332];
                    if (n_tmp332 == n_tmp334) {
                      for (unsigned in_tmp331 = 0,
                                    in_tmp331_end = n_tmp329.getNumChildren();
                           in_tmp331 < in_tmp331_end; in_tmp331++) {
                        TNode n_tmp331 = n_tmp329[in_tmp331];
                        if ((!(in_tmp332 == in_tmp331)) &&
                            ((n_tmp331).isConst()) && (n_tmp331 == n_tmp333)) {
                          if (Proof) {
                            proof->registerSwap(0, 0);
                            proof->registerRewrite(EQ_EQ_CONSTS);
                          };
                          Node rewritten_node = nm->mkConst(true);
                          return rewrite9<Proof>(rewritten_node, proof);
                        }
                      }
                    };
                    if (n_tmp332 == n_tmp334) {
                      for (unsigned in_tmp337 = 0,
                                    in_tmp337_end = n_tmp329.getNumChildren();
                           in_tmp337 < in_tmp337_end; in_tmp337++) {
                        TNode n_tmp337 = n_tmp329[in_tmp337];
                        if ((!(in_tmp332 == in_tmp337)) &&
                            (((((n_tmp337).isConst()) &&
                               ((n_tmp333).isConst())) &&
                              ((n_tmp337 != n_tmp333))) &&
                             ((n_tmp332)
                                  .getType()
                                  .getCardinality()
                                  .knownLessThanOrEqual(Cardinality(2))))) {
                          if (Proof) {
                            proof->registerSwap(0, 0);
                            proof->registerRewrite(EQ_NEQ_CONSTS_CARD2);
                          };
                          Node rewritten_node = nm->mkConst(false);
                          return rewrite9<Proof>(rewritten_node, proof);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };
  return rewrite8<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite11(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite12(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::EQUAL) && (true)) {
    for (unsigned in_tmp326 = 0, in_tmp326_end = node.getNumChildren();
         in_tmp326 < in_tmp326_end; in_tmp326++) {
      TNode n_tmp326 = node[in_tmp326];

      for (unsigned in_tmp325 = 0, in_tmp325_end = node.getNumChildren();
           in_tmp325 < in_tmp325_end; in_tmp325++) {
        TNode n_tmp325 = node[in_tmp325];
        if (!(in_tmp326 == in_tmp325)) {
          if (n_tmp325 == n_tmp326) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(X_EQ_X);
            };
            Node rewritten_node = nm->mkConst(true);
            return rewrite11<Proof>(rewritten_node, proof);
          };
          if (((n_tmp325).getKind() == kind::NOT) &&
              (n_tmp325[0] == n_tmp326)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(N_X_EQ_X);
            };
            Node rewritten_node = nm->mkConst(false);
            return rewrite11<Proof>(rewritten_node, proof);
          }
        }
      }
    }
  };
  return rewrite10<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite13(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite14(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::EQUAL) && (true)) {
    for (unsigned in_tmp322 = 0, in_tmp322_end = node.getNumChildren();
         in_tmp322 < in_tmp322_end; in_tmp322++) {
      TNode n_tmp322 = node[in_tmp322];

      for (unsigned in_tmp321 = 0, in_tmp321_end = node.getNumChildren();
           in_tmp321 < in_tmp321_end; in_tmp321++) {
        TNode n_tmp321 = node[in_tmp321];
        if ((!(in_tmp322 == in_tmp321)) &&
            ((n_tmp321).getKind() == kind::CONST_BOOLEAN)) {
          if (n_tmp321 == nm->mkConst(true)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(TRUE_EQ);
            };
            Node rewritten_node = n_tmp322;
            return rewrite13<Proof>(rewritten_node, proof);
          };
          if (n_tmp321 == nm->mkConst(false)) {
            if (Proof) {
              proof->registerSwap(0, 0);
              proof->registerRewrite(FALSE_EQ);
            };
            Node rewritten_node = nm->mkNode(kind::NOT, n_tmp322);
            return rewrite13<Proof>(rewritten_node, proof);
          }
        }
      }
    }
  };
  return rewrite12<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite15(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite16(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::IMPLIES) {
    if (((node[0]).getKind() == kind::CONST_BOOLEAN) && (true) &&
        (node[0] == nm->mkConst(true))) {
      if (Proof) {
        proof->registerRewrite(TRUE_IMPLIES);
      };
      Node rewritten_node = node[1];
      return rewrite15<Proof>(rewritten_node, proof);
    };
    if (((node[1]).getKind() == kind::CONST_BOOLEAN) && (true) &&
        (node[1] == nm->mkConst(false))) {
      if (Proof) {
        proof->registerRewrite(IMPLIES_FALSE);
      };
      Node rewritten_node = nm->mkNode(kind::NOT, node[0]);
      return rewrite15<Proof>(rewritten_node, proof);
    }
  };
  return rewrite14<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite17(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite18(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if ((node).getKind() == kind::IMPLIES) {
    if (((node[0]).getKind() == kind::CONST_BOOLEAN) && (true) &&
        (node[0] == nm->mkConst(false))) {
      if (Proof) {
        proof->registerRewrite(FALSE_IMPLIES);
      };
      Node rewritten_node = nm->mkConst(true);
      return rewrite17<Proof>(rewritten_node, proof);
    };
    if (((node[1]).getKind() == kind::CONST_BOOLEAN) && (true) &&
        (node[1] == nm->mkConst(true))) {
      if (Proof) {
        proof->registerRewrite(IMPLIES_TRUE);
      };
      Node rewritten_node = nm->mkConst(true);
      return rewrite17<Proof>(rewritten_node, proof);
    };
    if (((node[0]).getKind() == kind::CONST_BOOLEAN) &&
        ((node[1]).getKind() == kind::CONST_BOOLEAN) && (true) &&
        (node[0] == nm->mkConst(true)) && (node[1] == nm->mkConst(false))) {
      if (Proof) {
        proof->registerRewrite(TRUE_IMPLIES_FALSE);
      };
      Node rewritten_node = nm->mkConst(false);
      return rewrite17<Proof>(rewritten_node, proof);
    }
  };
  return rewrite16<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite19(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite20(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::AND) && (true)) {
    for (unsigned in_tmp318 = 0, in_tmp318_end = node.getNumChildren();
         in_tmp318 < in_tmp318_end; in_tmp318++) {
      TNode n_tmp318 = node[in_tmp318];
      if (((n_tmp318).getKind() == kind::CONST_BOOLEAN) &&
          (n_tmp318 == nm->mkConst(true))) {
        if (Proof) {
          proof->registerSwap(0, 0);
          proof->registerRewrite(AND_TRUE);
        };
        std::vector<Node> new_children =
            std::vector<Node>(node.begin(), node.end());
        ;
        new_children.erase(new_children.begin() + in_tmp318);
        Node x = mkCommutativeNode((node).getKind(), new_children);
        ;
        Node rewritten_node = x;
        return rewrite19<Proof>(rewritten_node, proof);
      };
      for (unsigned in_tmp319 = 0, in_tmp319_end = node.getNumChildren();
           in_tmp319 < in_tmp319_end; in_tmp319++) {
        TNode n_tmp319 = node[in_tmp319];
        if ((!(in_tmp318 == in_tmp319)) && (n_tmp319 == n_tmp318)) {
          if (Proof) {
            proof->registerSwap(0, 0);
            proof->registerRewrite(AND_DUP);
          };
          std::vector<Node> new_children =
              std::vector<Node>(node.begin(), node.end());
          ;
          new_children.erase(new_children.begin() + in_tmp319);
          new_children.erase(new_children.begin() + in_tmp318);
          Node x = mkCommutativeNode((node).getKind(), new_children);
          ;
          Node rewritten_node = nm->mkNode(kind::AND, n_tmp319, x);
          return rewrite19<Proof>(rewritten_node, proof);
        }
      }
    }
  };
  return rewrite18<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite21(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite22(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::AND) && (true)) {
    for (unsigned in_tmp317 = 0, in_tmp317_end = node.getNumChildren();
         in_tmp317 < in_tmp317_end; in_tmp317++) {
      TNode n_tmp317 = node[in_tmp317];
      if (((n_tmp317).getKind() == kind::CONST_BOOLEAN) &&
          (n_tmp317 == nm->mkConst(false))) {
        if (Proof) {
          proof->registerSwap(0, 0);
          proof->registerRewrite(AND_FALSE);
        };
        std::vector<Node> new_children =
            std::vector<Node>(node.begin(), node.end());
        ;
        new_children.erase(new_children.begin() + in_tmp317);
        Node x = mkCommutativeNode((node).getKind(), new_children);
        ;
        Node rewritten_node = nm->mkConst(false);
        return rewrite21<Proof>(rewritten_node, proof);
      }
    }
  };
  return rewrite20<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite23(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite24(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::OR) && (true)) {
    for (unsigned in_tmp314 = 0, in_tmp314_end = node.getNumChildren();
         in_tmp314 < in_tmp314_end; in_tmp314++) {
      TNode n_tmp314 = node[in_tmp314];
      if (((n_tmp314).getKind() == kind::CONST_BOOLEAN) &&
          (n_tmp314 == nm->mkConst(false))) {
        if (Proof) {
          proof->registerSwap(0, 0);
          proof->registerRewrite(OR_FALSE);
        };
        std::vector<Node> new_children =
            std::vector<Node>(node.begin(), node.end());
        ;
        new_children.erase(new_children.begin() + in_tmp314);
        Node x = mkCommutativeNode((node).getKind(), new_children);
        ;
        Node rewritten_node = x;
        return rewrite23<Proof>(rewritten_node, proof);
      };
      for (unsigned in_tmp315 = 0, in_tmp315_end = node.getNumChildren();
           in_tmp315 < in_tmp315_end; in_tmp315++) {
        TNode n_tmp315 = node[in_tmp315];
        if ((!(in_tmp314 == in_tmp315)) && (n_tmp315 == n_tmp314)) {
          if (Proof) {
            proof->registerSwap(0, 0);
            proof->registerRewrite(OR_DUP);
          };
          std::vector<Node> new_children =
              std::vector<Node>(node.begin(), node.end());
          ;
          new_children.erase(new_children.begin() + in_tmp315);
          new_children.erase(new_children.begin() + in_tmp314);
          Node x = mkCommutativeNode((node).getKind(), new_children);
          ;
          Node rewritten_node = nm->mkNode(kind::OR, n_tmp315, x);
          return rewrite23<Proof>(rewritten_node, proof);
        }
      }
    }
  };
  return rewrite22<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite25(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite26(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::OR) && (true)) {
    for (unsigned in_tmp313 = 0, in_tmp313_end = node.getNumChildren();
         in_tmp313 < in_tmp313_end; in_tmp313++) {
      TNode n_tmp313 = node[in_tmp313];
      if (((n_tmp313).getKind() == kind::CONST_BOOLEAN) &&
          (n_tmp313 == nm->mkConst(true))) {
        if (Proof) {
          proof->registerSwap(0, 0);
          proof->registerRewrite(OR_TRUE);
        };
        std::vector<Node> new_children =
            std::vector<Node>(node.begin(), node.end());
        ;
        new_children.erase(new_children.begin() + in_tmp313);
        Node x = mkCommutativeNode((node).getKind(), new_children);
        ;
        Node rewritten_node = nm->mkConst(true);
        return rewrite25<Proof>(rewritten_node, proof);
      }
    }
  };
  return rewrite24<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite27(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_AGAIN, node);
}

template <bool Proof>
inline RewriteResponse rewrite28(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::NOT) && ((node[0]).getKind() == kind::NOT) &&
      (true)) {
    if (Proof) {
      proof->registerRewrite(NOT_NOT);
    };
    Node rewritten_node = node[0][0];
    return rewrite27<Proof>(rewritten_node, proof);
  };
  return rewrite26<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse rewrite29(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  return RewriteResponse(REWRITE_DONE, node);
}

template <bool Proof>
inline RewriteResponse rewrite30(TNode node, RewriteProof *proof) {
  NodeManager *nm = NodeManager::currentNM();
  if (((node).getKind() == kind::NOT) &&
      ((node[0]).getKind() == kind::CONST_BOOLEAN) && (true)) {
    if (node[0] == nm->mkConst(true)) {
      if (Proof) {
        proof->registerRewrite(NOT_TRUE);
      };
      Node rewritten_node = nm->mkConst(false);
      return rewrite29<Proof>(rewritten_node, proof);
    };
    if (node[0] == nm->mkConst(false)) {
      if (Proof) {
        proof->registerRewrite(NOT_FALSE);
      };
      Node rewritten_node = nm->mkConst(true);
      return rewrite29<Proof>(rewritten_node, proof);
    }
  };
  return rewrite28<Proof>(node, proof);
}

template <bool Proof>
inline RewriteResponse bool_applyRules(TNode node, RewriteProof *proof) {

  return rewrite30<Proof>(node, proof);
}

inline void bool_printProof(bool use_cache, TheoryProofEngine *tp,
                            const Rewrite *rewrite, std::ostream &os,
                            ProofLetMap &globalLetMap) {

  if (rewrite->d_tag == NOT_TRUE) {
    os << "(not_true _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == NOT_FALSE) {
    os << "(not_false _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == NOT_NOT) {
    os << "(not_not _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == OR_TRUE) {
    os << "(or_true _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == OR_FALSE) {
    os << "(or_false _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == OR_DUP) {
    os << "(or_dup _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == AND_FALSE) {
    os << "(and_false _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == AND_TRUE) {
    os << "(and_true _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == AND_DUP) {
    os << "(and_dup _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == FALSE_IMPLIES) {
    os << "(false_implies _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == IMPLIES_TRUE) {
    os << "(implies_true _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == TRUE_IMPLIES_FALSE) {
    os << "(true_implies_false _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == TRUE_IMPLIES) {
    os << "(true_implies _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == IMPLIES_FALSE) {
    os << "(implies_false _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == TRUE_EQ) {
    os << "(true_eq _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == FALSE_EQ) {
    os << "(false_eq _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == X_EQ_X) {
    os << "(x_eq_x _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == N_X_EQ_X) {
    os << "(n_x_eq_x _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == EQ_EQ_CONSTS) {
    os << "(eq_eq_consts _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == EQ_NEQ_CONSTS_CARD2) {
    os << "(eq_neq_consts_card2 _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == EQ_NEQ_CONSTS) {
    os << "(eq_neq_consts _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == TRUE_XOR) {
    os << "(true_xor _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == FALSE_XOR) {
    os << "(false_xor _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == X_XOR_X) {
    os << "(x_xor_x _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == N_X_XOR_X) {
    os << "(n_x_xor_x _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_TRUE) {
    os << "(ite_true _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_FALSE) {
    os << "(ite_false _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_X_TRUE_FALSE) {
    os << "(ite_x_true_false _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_FALSE_TRUE) {
    os << "(ite_c_false_true _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_X_X) {
    os << "(ite_c_x_x _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_X_N_X) {
    os << "(ite_c_x_n_x _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_N_X_X) {
    os << "(ite_c_n_x_x _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_X_X_Y) {
    os << "(ite_x_x_y _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_N_X_X_Y) {
    os << "(ite_n_x_x_y _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_X_N_X_Y) {
    os << "(ite_x_n_x_y _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_X_Y_X) {
    os << "(ite_x_y_x _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_N_X_Y_X) {
    os << "(ite_n_x_y_x _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_X_Y_N_X) {
    os << "(ite_x_y_n_x _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_ITE_C_X_Y_Z) {
    os << "(ite_c_ite_c_x_y_z _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_ITE_N_C_X_Y_Z) {
    os << "(ite_c_ite_n_c_x_y_z _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_N_C_ITE_C_X_Y_Z) {
    os << "(ite_n_c_ite_c_x_y_z _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_Z_ITE_C_X_Y) {
    os << "(ite_c_z_ite_c_x_y _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_C_Z_ITE_N_C_X_Y) {
    os << "(ite_c_z_ite_n_c_x_y _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  } else if (rewrite->d_tag == ITE_N_C_Z_ITE_C_X_Y) {
    os << "(ite_n_c_z_ite_c_x_y _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(use_cache, tp, rewrite->d_children[0], os,
                          globalLetMap);
    os << ")";
  }
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
