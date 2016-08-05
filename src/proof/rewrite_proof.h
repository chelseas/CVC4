#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "proof/theory_proof.h"
#include "util/proof.h"

namespace CVC4 {

typedef int rewrite_tag_t;

// Theory independent rewrites
enum SharedRewrites {
  ORIGINAL_OP, // Mirror an original operator
  TRUSTED,
  SWAP,
  LAST_SHARED,
};

struct Rewrite {
  // The type of the rewrite
  int d_tag;
  // Node before the rewrite
  Node d_original;
  // Rewrite proofs for children
  std::vector<Rewrite *> d_children;
  // Subproofs
  std::vector<Rewrite *> d_subproofs;
  // Unique id to identify the rewrite
  unsigned d_id;
  // Stores whether the cached version of this rewrite is ever used
  bool d_cached_version_used;
  // XXX: refactor into seperate class
  unsigned swap_id1, swap_id2;

  Rewrite(const Node original)
      : d_tag(0), d_original(original), d_cached_version_used(false) {
    d_id = ProofLetCount::newId();
  }
  Rewrite(const rewrite_tag_t tag, const Node original)
      : d_tag(tag), d_original(original), d_cached_version_used(false) {
    d_id = ProofLetCount::newId();
  }
  ~Rewrite();

  void deleteUncachedChildren();
  void print(int tab) const;
  bool isLeaf() const { return d_children.size() == 0; }
};

typedef __gnu_cxx::hash_map<Node, Rewrite *, NodeHashFunction> ProofCache;
typedef __gnu_cxx::hash_map<Node, Rewrite *, NodeHashFunction>::const_iterator
    ProofCacheIterator;

class RewriteProof {
private:
  std::vector<Rewrite *> d_rewrites;
  ProofCache preRewriteCache;
  ProofCache postRewriteCache;

public:
  RewriteProof() {}
  ~RewriteProof();

  void addRewrite(Rewrite *rewrite) { d_rewrites.push_back(rewrite); }

  void attachSubproofToParent();

  Rewrite *getRewrite() const;
  Rewrite *getTopRewrite() const { return d_rewrites.back(); };

  void registerRewrite(const int tag);
  void registerSwap(const unsigned swap_id1, const unsigned swap_id2);
  void replaceRewrite(Rewrite *rewrite);

  Rewrite *getPreRewriteCache(Node node);
  Rewrite *getPostRewriteCache(Node node);
  void setPreRewriteCache(Node node, Rewrite *rewrite);
  void setPostRewriteCache(Node node, Rewrite *rewrite);

  void printCachedProofs(TheoryProofEngine *tp, std::ostream &os,
                         std::ostream &paren, ProofLetMap &globalLetMap) const;
};

} /* CVC4 namespace */
