/*********************                                                        */
/*! \file synth_conjecture.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Class that encapsulates techniques for a single (SyGuS) synthesis
 ** conjecture.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYNTH_CONJECTURE_H
#define __CVC4__THEORY__QUANTIFIERS__SYNTH_CONJECTURE_H

#include <memory>

#include "theory/decision_manager.h"
#include "theory/quantifiers/expr_miner_manager.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"
#include "theory/quantifiers/sygus/cegis.h"
#include "theory/quantifiers/sygus/cegis_unif.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/sygus_pbe.h"
#include "theory/quantifiers/sygus/sygus_process_conj.h"
#include "theory/quantifiers/sygus/sygus_repair_const.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** a synthesis conjecture
 * This class implements approaches for a synthesis conecjture, given by data
 * member d_quant.
 * This includes both approaches for synthesis in Reynolds et al CAV 2015. It
 * determines which approach and optimizations are applicable to the
 * conjecture, and has interfaces for implementing them.
 */
class SynthConjecture
{
 public:
  SynthConjecture(QuantifiersEngine* qe);
  ~SynthConjecture();
  /** get original version of conjecture */
  Node getConjecture() { return d_quant; }
  /** get deep embedding version of conjecture */
  Node getEmbeddedConjecture() { return d_embed_quant; }
  //-------------------------------for counterexample-guided check/refine
  /** increment the number of times we have successfully done candidate
   * refinement */
  void incrementRefineCount() { d_refine_count++; }
  /** whether the conjecture is waiting for a call to doCheck below */
  bool needsCheck();
  /** whether the conjecture is waiting for a call to doRefine below */
  bool needsRefinement() const;
  /** do single invocation check
   * This updates Gamma for an iteration of step 2 of Figure 1 of Reynolds et al
   * CAV 2015.
   */
  void doSingleInvCheck(std::vector<Node>& lems);
  /** do syntax-guided enumerative check
   * This is step 2(a) of Figure 3 of Reynolds et al CAV 2015.
   */
  void doCheck(std::vector<Node>& lems);
  /** do refinement
   * This is step 2(b) of Figure 3 of Reynolds et al CAV 2015.
   */
  void doRefine(std::vector<Node>& lems);
  //-------------------------------end for counterexample-guided check/refine
  /**
   * prints the synthesis solution to output stream out.
   *
   * singleInvocation : set to true if we should consult the single invocation
   * module to get synthesis solutions.
   */
  void printSynthSolution(std::ostream& out, bool singleInvocation);
  /** get synth solutions
   *
   * This returns a map from function-to-synthesize variables to their
   * builtin solution, which has the same type. For example, for synthesis
   * conjecture exists f. forall x. f( x )>x, this function may return the map
   * containing the entry:
   *   f -> (lambda x. x+1)
   *
   * singleInvocation : set to true if we should consult the single invocation
   * module to get synthesis solutions.
   */
  void getSynthSolutions(std::map<Node, Node>& sol_map, bool singleInvocation);
  /**
   * The feasible guard whose semantics are "this conjecture is feasiable".
   * This is "G" in Figure 3 of Reynolds et al CAV 2015.
   */
  Node getGuard() const;
  /** is ground */
  bool isGround() { return d_inner_vars.empty(); }
  /** are we using single invocation techniques */
  bool isSingleInvocation() const;
  /** preregister conjecture
   * This is used as a heuristic for solution reconstruction, so that we
   * remember expressions in the conjecture before preprocessing, since they
   * may be helpful during solution reconstruction (Figure 5 of Reynolds et al
   * CAV 2015)
   */
  void preregisterConjecture(Node q);
  /** assign conjecture q to this class */
  void assign(Node q);
  /** has a conjecture been assigned to this class */
  bool isAssigned() { return !d_embed_quant.isNull(); }
  /** get model values for terms n, store in vector v */
  void getModelValues(std::vector<Node>& n, std::vector<Node>& v);
  /** get model value for term n */
  Node getModelValue(Node n);

  /** get utility for static preprocessing and analysis of conjectures */
  SynthConjectureProcess* getProcess() { return d_ceg_proc.get(); }
  /** get constant repair utility */
  SygusRepairConst* getRepairConst() { return d_sygus_rconst.get(); }
  /** get program by examples module */
  SygusPbe* getPbe() { return d_ceg_pbe.get(); }
  /** get the symmetry breaking predicate for type */
  Node getSymmetryBreakingPredicate(
      Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth);
  /** print out debug information about this conjecture */
  void debugPrint(const char* c);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** The feasible guard. */
  Node d_feasible_guard;
  /** the decision strategy for the feasible guard */
  std::unique_ptr<DecisionStrategy> d_feasible_strategy;
  /** single invocation utility */
  std::unique_ptr<CegSingleInv> d_ceg_si;
  /** utility for static preprocessing and analysis of conjectures */
  std::unique_ptr<SynthConjectureProcess> d_ceg_proc;
  /** grammar utility */
  std::unique_ptr<CegGrammarConstructor> d_ceg_gc;
  /** repair constant utility */
  std::unique_ptr<SygusRepairConst> d_sygus_rconst;

  //------------------------modules
  /** program by examples module */
  std::unique_ptr<SygusPbe> d_ceg_pbe;
  /** CEGIS module */
  std::unique_ptr<Cegis> d_ceg_cegis;
  /** CEGIS UNIF module */
  std::unique_ptr<CegisUnif> d_ceg_cegisUnif;
  /** the set of active modules (subset of the above list) */
  std::vector<SygusModule*> d_modules;
  /** master module
   *
   * This is the module (one of those above) that takes sole responsibility
   * for this conjecture, determined during assign(...).
   */
  SygusModule* d_master;
  //------------------------end modules

  /** list of constants for quantified formula
   * The outer Skolems for the negation of d_embed_quant.
   */
  std::vector<Node> d_candidates;
  /** base instantiation
   * If d_embed_quant is forall d. exists y. P( d, y ), then
   * this is the formula  exists y. P( d_candidates, y ). Notice that
   * (exists y. F) is shorthand above for ~( forall y. ~F ).
   */
  Node d_base_inst;
  /** list of variables on inner quantification */
  std::vector<Node> d_inner_vars;
  /**
   * The set of skolems for the current "verification" lemma, if one exists.
   * This may be added to during calls to doCheck(). The model values for these
   * skolems are analyzed during doRefine().
   */
  std::vector<Node> d_ce_sk_vars;
  /**
   * If we have already tested the satisfiability of the current verification
   * lemma, this stores the model values of d_ce_sk_vars in the current
   * (satisfiable, failed) verification lemma.
   */
  std::vector<Node> d_ce_sk_var_mvs;
  /**
   * Whether the above vector has been set. We have this flag since the above
   * vector may be set to empty (e.g. for ground synthesis conjectures).
   */
  bool d_set_ce_sk_vars;

  /** the asserted (negated) conjecture */
  Node d_quant;
  /** (negated) conjecture after simplification */
  Node d_simp_quant;
  /** (negated) conjecture after simplification, conversion to deep embedding */
  Node d_embed_quant;
  /** candidate information */
  class CandidateInfo
  {
   public:
    CandidateInfo() {}
    /** list of terms we have instantiated candidates with */
    std::vector<Node> d_inst;
  };
  std::map<Node, CandidateInfo> d_cinfo;
  /**
   * The first index of an instantiation in CandidateInfo::d_inst that we have
   * not yet tried to repair.
   */
  unsigned d_repair_index;
  /** number of times we have called doRefine */
  unsigned d_refine_count;
  /** get candidadate */
  Node getCandidate(unsigned int i) { return d_candidates[i]; }
  /** record instantiation (this is used to construct solutions later) */
  void recordInstantiation(std::vector<Node>& vs)
  {
    Assert(vs.size() == d_candidates.size());
    for (unsigned i = 0; i < vs.size(); i++)
    {
      d_cinfo[d_candidates[i]].d_inst.push_back(vs[i]);
    }
  }
  /** get synth solutions internal
   *
   * This function constructs the body of solutions for all
   * functions-to-synthesize in this conjecture and stores them in sols, in
   * order. For each solution added to sols, we add an integer indicating what
   * kind of solution n is, where if sols[i] = n, then
   *   if status[i] = 0: n is the (builtin term) corresponding to the solution,
   *   if status[i] = 1: n is the sygus representation of the solution.
   * We store builtin versions under some conditions (such as when the sygus
   * grammar is being ignored).
   *
   * singleInvocation : set to true if we should consult the single invocation
   * module to get synthesis solutions.
   *
   * For example, for conjecture exists fg. forall x. f(x)>g(x), this function
   * may set ( sols, status ) to ( { x+1, d_x() }, { 1, 0 } ), where d_x() is
   * the sygus datatype constructor corresponding to variable x.
   */
  bool getSynthSolutionsInternal(std::vector<Node>& sols,
                                 std::vector<int>& status,
                                 bool singleInvocation);
  //-------------------------------- sygus stream
  /** current stream guard */
  Node d_current_stream_guard;
  /** the decision strategy for streaming solutions */
  class SygusStreamDecisionStrategy : public DecisionStrategyFmf
  {
   public:
    SygusStreamDecisionStrategy(context::Context* satContext,
                                Valuation valuation);
    /** make literal */
    Node mkLiteral(unsigned i) override;
    /** identify */
    std::string identify() const override
    {
      return std::string("sygus_stream");
    }
  };
  std::unique_ptr<SygusStreamDecisionStrategy> d_stream_strategy;
  /** get current stream guard */
  Node getCurrentStreamGuard() const;
  /** get stream guarded lemma
   *
   * If sygusStream is enabled, this returns ( G V n ) where G is the guard
   * returned by getCurrentStreamGuard, otherwise this returns n.
   */
  Node getStreamGuardedLemma(Node n) const;
  /**
   * Prints the current synthesis solution to the output stream indicated by
   * the Options object, send a lemma blocking the current solution to the
   * output channel.
   */
  void printAndContinueStream();
  //-------------------------------- end sygus stream
  /** expression miner managers for each function-to-synthesize
   *
   * Notice that for each function-to-synthesize, we enumerate a stream of
   * candidate solutions, where each of these streams is independent. Thus,
   * we maintain separate expression miner managers for each of them.
   *
   * This is used for the sygusRewSynth() option to synthesize new candidate
   * rewrite rules.
   */
  std::map<Node, ExpressionMinerManager> d_exprm;
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
