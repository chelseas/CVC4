/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"

#include <algorithm>
#include <cctype>
#include <iterator>
#include <memory>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/exception.h"
#include "base/listener.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "decision/decision_engine.h"
#include "expr/attribute.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_self_iterator.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_mode.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "preprocessing/passes/apply_substs.h"
#include "preprocessing/passes/apply_to_const.h"
#include "preprocessing/passes/bool_to_bv.h"
#include "preprocessing/passes/bv_abstraction.h"
#include "preprocessing/passes/bv_ackermann.h"
#include "preprocessing/passes/bv_eager_atoms.h"
#include "preprocessing/passes/bv_gauss.h"
#include "preprocessing/passes/bv_intro_pow2.h"
#include "preprocessing/passes/bv_to_bool.h"
#include "preprocessing/passes/extended_rewriter_pass.h"
#include "preprocessing/passes/global_negate.h"
#include "preprocessing/passes/int_to_bv.h"
#include "preprocessing/passes/ite_removal.h"
#include "preprocessing/passes/ite_simp.h"
#include "preprocessing/passes/miplib_trick.h"
#include "preprocessing/passes/nl_ext_purify.h"
#include "preprocessing/passes/non_clausal_simp.h"
#include "preprocessing/passes/pseudo_boolean_processor.h"
#include "preprocessing/passes/quantifier_macros.h"
#include "preprocessing/passes/quantifiers_preprocess.h"
#include "preprocessing/passes/real_to_int.h"
#include "preprocessing/passes/rewrite.h"
#include "preprocessing/passes/sep_skolem_emp.h"
#include "preprocessing/passes/sort_infer.h"
#include "preprocessing/passes/static_learning.h"
#include "preprocessing/passes/sygus_inference.h"
#include "preprocessing/passes/symmetry_breaker.h"
#include "preprocessing/passes/symmetry_detect.h"
#include "preprocessing/passes/synth_rew_rules.h"
#include "preprocessing/passes/theory_preprocess.h"
#include "preprocessing/passes/unconstrained_simplifier.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "printer/printer.h"
#include "proof/proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/command.h"
#include "smt/command_list.h"
#include "smt/logic_request.h"
#include "smt/managed_ostreams.h"
#include "smt/model_core_builder.h"
#include "smt/smt_engine_scope.h"
#include "smt/term_formula_removal.h"
#include "smt/update_ostream.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/nary_builder.h"
#include "smt_util/node_visitor.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/strings/theory_strings.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "util/hash.h"
#include "util/proof.h"
#include "util/random.h"
#include "util/resource_manager.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::preprocessing::passes;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

struct DeleteCommandFunction : public std::unary_function<const Command*, void>
{
  void operator()(const Command* command) { delete command; }
};

void DeleteAndClearCommandVector(std::vector<Command*>& commands) {
  std::for_each(commands.begin(), commands.end(), DeleteCommandFunction());
  commands.clear();
}

/** Useful for counting the number of recursive calls. */
class ScopeCounter {
private:
  unsigned& d_depth;
public:
  ScopeCounter(unsigned& d) : d_depth(d) {
    ++d_depth;
  }
  ~ScopeCounter(){
    --d_depth;
  }
};

/**
 * Representation of a defined function.  We keep these around in
 * SmtEngine to permit expanding definitions late (and lazily), to
 * support getValue() over defined functions, to support user output
 * in terms of defined functions, etc.
 */
class DefinedFunction {
  Node d_func;
  vector<Node> d_formals;
  Node d_formula;
public:
  DefinedFunction() {}
  DefinedFunction(Node func, vector<Node> formals, Node formula) :
    d_func(func),
    d_formals(formals),
    d_formula(formula) {
  }
  Node getFunction() const { return d_func; }
  vector<Node> getFormals() const { return d_formals; }
  Node getFormula() const { return d_formula; }
};/* class DefinedFunction */

struct SmtEngineStatistics {
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** number of constant propagations found during nonclausal simp */
  IntStat d_numConstantProps;
  /** time spent converting to CNF */
  TimerStat d_cnfConversionTime;
  /** Num of assertions before ite removal */
  IntStat d_numAssertionsPre;
  /** Num of assertions after ite removal */
  IntStat d_numAssertionsPost;
  /** time spent in checkModel() */
  TimerStat d_checkModelTime;
  /** time spent in checkProof() */
  TimerStat d_checkProofTime;
  /** time spent in checkUnsatCore() */
  TimerStat d_checkUnsatCoreTime;
  /** time spent in PropEngine::checkSat() */
  TimerStat d_solveTime;
  /** time spent in pushing/popping */
  TimerStat d_pushPopTime;
  /** time spent in processAssertions() */
  TimerStat d_processAssertionsTime;

  /** Has something simplified to false? */
  IntStat d_simplifiedToFalse;
  /** Number of resource units spent. */
  ReferenceStat<uint64_t> d_resourceUnitsUsed;

  SmtEngineStatistics() :
    d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
    d_numConstantProps("smt::SmtEngine::numConstantProps", 0),
    d_cnfConversionTime("smt::SmtEngine::cnfConversionTime"),
    d_numAssertionsPre("smt::SmtEngine::numAssertionsPreITERemoval", 0),
    d_numAssertionsPost("smt::SmtEngine::numAssertionsPostITERemoval", 0),
    d_checkModelTime("smt::SmtEngine::checkModelTime"),
    d_checkProofTime("smt::SmtEngine::checkProofTime"),
    d_checkUnsatCoreTime("smt::SmtEngine::checkUnsatCoreTime"),
    d_solveTime("smt::SmtEngine::solveTime"),
    d_pushPopTime("smt::SmtEngine::pushPopTime"),
    d_processAssertionsTime("smt::SmtEngine::processAssertionsTime"),
    d_simplifiedToFalse("smt::SmtEngine::simplifiedToFalse", 0),
    d_resourceUnitsUsed("smt::SmtEngine::resourceUnitsUsed")
 {
    smtStatisticsRegistry()->registerStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->registerStat(&d_numConstantProps);
    smtStatisticsRegistry()->registerStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->registerStat(&d_checkModelTime);
    smtStatisticsRegistry()->registerStat(&d_checkProofTime);
    smtStatisticsRegistry()->registerStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->registerStat(&d_solveTime);
    smtStatisticsRegistry()->registerStat(&d_pushPopTime);
    smtStatisticsRegistry()->registerStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->registerStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->registerStat(&d_resourceUnitsUsed);
  }

  ~SmtEngineStatistics() {
    smtStatisticsRegistry()->unregisterStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
    smtStatisticsRegistry()->unregisterStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->unregisterStat(&d_checkModelTime);
    smtStatisticsRegistry()->unregisterStat(&d_checkProofTime);
    smtStatisticsRegistry()->unregisterStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->unregisterStat(&d_solveTime);
    smtStatisticsRegistry()->unregisterStat(&d_pushPopTime);
    smtStatisticsRegistry()->unregisterStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->unregisterStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->unregisterStat(&d_resourceUnitsUsed);
  }
};/* struct SmtEngineStatistics */


class SoftResourceOutListener : public Listener {
 public:
  SoftResourceOutListener(SmtEngine& smt) : d_smt(&smt) {}
  void notify() override
  {
    SmtScope scope(d_smt);
    Assert(smt::smtEngineInScope());
    d_smt->interrupt();
  }
 private:
  SmtEngine* d_smt;
}; /* class SoftResourceOutListener */


class HardResourceOutListener : public Listener {
 public:
  HardResourceOutListener(SmtEngine& smt) : d_smt(&smt) {}
  void notify() override
  {
    SmtScope scope(d_smt);
    theory::Rewriter::clearCaches();
  }
 private:
  SmtEngine* d_smt;
}; /* class HardResourceOutListener */

class SetLogicListener : public Listener {
 public:
  SetLogicListener(SmtEngine& smt) : d_smt(&smt) {}
  void notify() override
  {
    LogicInfo inOptions(options::forceLogicString());
    d_smt->setLogic(inOptions);
  }
 private:
  SmtEngine* d_smt;
}; /* class SetLogicListener */

class BeforeSearchListener : public Listener {
 public:
  BeforeSearchListener(SmtEngine& smt) : d_smt(&smt) {}
  void notify() override { d_smt->beforeSearch(); }

 private:
  SmtEngine* d_smt;
}; /* class BeforeSearchListener */

class UseTheoryListListener : public Listener {
 public:
  UseTheoryListListener(TheoryEngine* theoryEngine)
      : d_theoryEngine(theoryEngine)
  {}

  void notify() override
  {
    std::stringstream commaList(options::useTheoryList());
    std::string token;

    Debug("UseTheoryListListener") << "UseTheoryListListener::notify() "
                                   << options::useTheoryList() << std::endl;

    while(std::getline(commaList, token, ',')){
      if(token == "help") {
        puts(theory::useTheoryHelp);
        exit(1);
      }
      if(theory::useTheoryValidate(token)) {
        d_theoryEngine->enableTheoryAlternative(token);
      } else {
        throw OptionException(
            std::string("unknown option for --use-theory : `") + token +
            "'.  Try --use-theory=help.");
      }
    }
  }

 private:
  TheoryEngine* d_theoryEngine;
}; /* class UseTheoryListListener */


class SetDefaultExprDepthListener : public Listener {
 public:
  void notify() override
  {
    int depth = options::defaultExprDepth();
    Debug.getStream() << expr::ExprSetDepth(depth);
    Trace.getStream() << expr::ExprSetDepth(depth);
    Notice.getStream() << expr::ExprSetDepth(depth);
    Chat.getStream() << expr::ExprSetDepth(depth);
    Message.getStream() << expr::ExprSetDepth(depth);
    Warning.getStream() << expr::ExprSetDepth(depth);
    // intentionally exclude Dump stream from this list
  }
};

class SetDefaultExprDagListener : public Listener {
 public:
  void notify() override
  {
    int dag = options::defaultDagThresh();
    Debug.getStream() << expr::ExprDag(dag);
    Trace.getStream() << expr::ExprDag(dag);
    Notice.getStream() << expr::ExprDag(dag);
    Chat.getStream() << expr::ExprDag(dag);
    Message.getStream() << expr::ExprDag(dag);
    Warning.getStream() << expr::ExprDag(dag);
    Dump.getStream() << expr::ExprDag(dag);
  }
};

class SetPrintExprTypesListener : public Listener {
 public:
  void notify() override
  {
    bool value = options::printExprTypes();
    Debug.getStream() << expr::ExprPrintTypes(value);
    Trace.getStream() << expr::ExprPrintTypes(value);
    Notice.getStream() << expr::ExprPrintTypes(value);
    Chat.getStream() << expr::ExprPrintTypes(value);
    Message.getStream() << expr::ExprPrintTypes(value);
    Warning.getStream() << expr::ExprPrintTypes(value);
    // intentionally exclude Dump stream from this list
  }
};

class DumpModeListener : public Listener {
 public:
  void notify() override
  {
    const std::string& value = options::dumpModeString();
    Dump.setDumpFromString(value);
  }
};

class PrintSuccessListener : public Listener {
 public:
  void notify() override
  {
    bool value = options::printSuccess();
    Debug.getStream() << Command::printsuccess(value);
    Trace.getStream() << Command::printsuccess(value);
    Notice.getStream() << Command::printsuccess(value);
    Chat.getStream() << Command::printsuccess(value);
    Message.getStream() << Command::printsuccess(value);
    Warning.getStream() << Command::printsuccess(value);
    *options::out() << Command::printsuccess(value);
  }
};



/**
 * This is an inelegant solution, but for the present, it will work.
 * The point of this is to separate the public and private portions of
 * the SmtEngine class, so that smt_engine.h doesn't
 * include "expr/node.h", which is a private CVC4 header (and can lead
 * to linking errors due to the improper inlining of non-visible symbols
 * into user code!).
 *
 * The "real" solution (that which is usually implemented) is to move
 * ALL the implementation to SmtEnginePrivate and maintain a
 * heap-allocated instance of it in SmtEngine.  SmtEngine (the public
 * one) becomes an "interface shell" which simply acts as a forwarder
 * of method calls.
 */
class SmtEnginePrivate : public NodeManagerListener {
  SmtEngine& d_smt;

  typedef unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
  typedef unordered_map<Node, bool, NodeHashFunction> NodeToBoolHashMap;

  /**
   * Manager for limiting time and abstract resource usage.
   */
  ResourceManager* d_resourceManager;

  /** Manager for the memory of regular-output-channel. */
  ManagedRegularOutputChannel d_managedRegularChannel;

  /** Manager for the memory of diagnostic-output-channel. */
  ManagedDiagnosticOutputChannel d_managedDiagnosticChannel;

  /** Manager for the memory of --dump-to. */
  ManagedDumpOStream d_managedDumpChannel;

  /** Manager for --replay-log. */
  ManagedReplayLogOstream d_managedReplayLog;

  /**
   * This list contains:
   *  softResourceOut
   *  hardResourceOut
   *  setForceLogic
   *  beforeSearchListener
   *  UseTheoryListListener
   *
   * This needs to be deleted before both NodeManager's Options,
   * SmtEngine, d_resourceManager, and TheoryEngine.
   */
  ListenerRegistrationList* d_listenerRegistrations;

  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;

  /** Assertions in the preprocessing pipeline */
  AssertionPipeline d_assertions;

  /** Whether any assertions have been processed */
  CDO<bool> d_assertionsProcessed;

  // Cached true value
  Node d_true;

  /**
   * A context that never pushes/pops, for use by CD structures (like
   * SubstitutionMaps) that should be "global".
   */
  context::Context d_fakeContext;

  /**
   * A map of AbsractValues to their actual constants.  Only used if
   * options::abstractValues() is on.
   */
  SubstitutionMap d_abstractValueMap;

  /**
   * A mapping of all abstract values (actual value |-> abstract) that
   * we've handed out.  This is necessary to ensure that we give the
   * same AbstractValues for the same real constants.  Only used if
   * options::abstractValues() is on.
   */
  NodeToNodeHashMap d_abstractValues;

  /** Number of calls of simplify assertions active.
   */
  unsigned d_simplifyAssertionsDepth;

  /** TODO: whether certain preprocess steps are necessary */
  //bool d_needsExpandDefs;

  //------------------------------- expression names
  /** mapping from expressions to name */
  context::CDHashMap< Node, std::string, NodeHashFunction > d_exprNames;
  //------------------------------- end expression names
 public:
  IteSkolemMap& getIteSkolemMap() { return d_assertions.getIteSkolemMap(); }

  /** Instance of the ITE remover */
  RemoveTermFormulas d_iteRemover;

  /* Finishes the initialization of the private portion of SMTEngine. */
  void finishInit();

 private:
  std::unique_ptr<PreprocessingPassContext> d_preprocessingPassContext;
  PreprocessingPassRegistry d_preprocessingPassRegistry;

  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  void collectSkolems(TNode n, set<TNode>& skolemSet, NodeToBoolHashMap& cache);

  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  bool checkForBadSkolems(TNode n, TNode skolem, NodeToBoolHashMap& cache);

  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions();

 public:
  SmtEnginePrivate(SmtEngine& smt)
      : d_smt(smt),
        d_managedRegularChannel(),
        d_managedDiagnosticChannel(),
        d_managedDumpChannel(),
        d_managedReplayLog(),
        d_listenerRegistrations(new ListenerRegistrationList()),
        d_propagator(true, true),
        d_assertions(),
        d_assertionsProcessed(smt.d_userContext, false),
        d_fakeContext(),
        d_abstractValueMap(&d_fakeContext),
        d_abstractValues(),
        d_simplifyAssertionsDepth(0),
        // d_needsExpandDefs(true),  //TODO?
        d_exprNames(smt.d_userContext),
        d_iteRemover(smt.d_userContext)
  {
    d_smt.d_nodeManager->subscribeEvents(this);
    d_true = NodeManager::currentNM()->mkConst(true);
    d_resourceManager = NodeManager::currentResourceManager();

    d_listenerRegistrations->add(d_resourceManager->registerSoftListener(
        new SoftResourceOutListener(d_smt)));

    d_listenerRegistrations->add(d_resourceManager->registerHardListener(
        new HardResourceOutListener(d_smt)));

    Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
    d_listenerRegistrations->add(
        nodeManagerOptions.registerForceLogicListener(
            new SetLogicListener(d_smt), true));

    // Multiple options reuse BeforeSearchListener so registration requires an
    // extra bit of care.
    // We can safely not call notify on this before search listener at
    // registration time. This d_smt cannot be beforeSearch at construction
    // time. Therefore the BeforeSearchListener is a no-op. Therefore it does
    // not have to be called.
    d_listenerRegistrations->add(
        nodeManagerOptions.registerBeforeSearchListener(
            new BeforeSearchListener(d_smt)));

    // These do need registration calls.
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDefaultExprDepthListener(
            new SetDefaultExprDepthListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDefaultExprDagListener(
            new SetDefaultExprDagListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetPrintExprTypesListener(
            new SetPrintExprTypesListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDumpModeListener(
            new DumpModeListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetPrintSuccessListener(
            new PrintSuccessListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetRegularOutputChannelListener(
            new SetToDefaultSourceListener(&d_managedRegularChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDiagnosticOutputChannelListener(
            new SetToDefaultSourceListener(&d_managedDiagnosticChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerDumpToFileNameListener(
            new SetToDefaultSourceListener(&d_managedDumpChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetReplayLogFilename(
            new SetToDefaultSourceListener(&d_managedReplayLog), true));
  }

  ~SmtEnginePrivate()
  {
    delete d_listenerRegistrations;

    if(d_propagator.getNeedsFinish()) {
      d_propagator.finish();
      d_propagator.setNeedsFinish(false);
    }
    d_smt.d_nodeManager->unsubscribeEvents(this);
  }

  void unregisterPreprocessingPasses()
  {
    d_preprocessingPassRegistry.unregisterPasses();
  }

  ResourceManager* getResourceManager() { return d_resourceManager; }
  void spendResource(unsigned amount)
  {
    d_resourceManager->spendResource(amount);
  }

  void nmNotifyNewSort(TypeNode tn, uint32_t flags) override
  {
    DeclareTypeCommand c(tn.getAttribute(expr::VarNameAttr()),
                         0,
                         tn.toType());
    if((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0) {
      d_smt.addToModelCommandAndDump(c, flags);
    }
  }

  void nmNotifyNewSortConstructor(TypeNode tn, uint32_t flags) override
  {
    DeclareTypeCommand c(tn.getAttribute(expr::VarNameAttr()),
                         tn.getAttribute(expr::SortArityAttr()),
                         tn.toType());
    if ((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0)
    {
      d_smt.addToModelCommandAndDump(c);
    }
  }

  void nmNotifyNewDatatypes(const std::vector<DatatypeType>& dtts,
                            uint32_t flags) override
  {
    if ((flags & ExprManager::DATATYPE_FLAG_PLACEHOLDER) == 0)
    {
      DatatypeDeclarationCommand c(dtts);
      d_smt.addToModelCommandAndDump(c);
    }
  }

  void nmNotifyNewVar(TNode n, uint32_t flags) override
  {
    DeclareFunctionCommand c(n.getAttribute(expr::VarNameAttr()),
                             n.toExpr(),
                             n.getType().toType());
    if((flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
      d_smt.addToModelCommandAndDump(c, flags);
    }
  }

  void nmNotifyNewSkolem(TNode n,
                         const std::string& comment,
                         uint32_t flags) override
  {
    string id = n.getAttribute(expr::VarNameAttr());
    DeclareFunctionCommand c(id, n.toExpr(), n.getType().toType());
    if(Dump.isOn("skolems") && comment != "") {
      Dump("skolems") << CommentCommand(id + " is " + comment);
    }
    if((flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
      d_smt.addToModelCommandAndDump(c, flags, false, "skolems");
    }
  }

  void nmNotifyDeleteNode(TNode n) override {}

  Node applySubstitutions(TNode node)
  {
    return Rewriter::rewrite(
        d_preprocessingPassContext->getTopLevelSubstitutions().apply(node));
  }

  /**
   * Process the assertions that have been asserted.
   */
  void processAssertions();

  /** Process a user push.
  */
  void notifyPush() {

  }

  /**
   * Process a user pop.  Clears out the non-context-dependent stuff in this
   * SmtEnginePrivate.  Necessary to clear out our assertion vectors in case
   * someone does a push-assert-pop without a check-sat. It also pops the
   * last map of expression names from notifyPush.
   */
  void notifyPop() {
    d_assertions.clear();
    d_propagator.getLearnedLiterals().clear();
    getIteSkolemMap().clear();
  }

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   * the 2nd and 3rd arguments added for bookkeeping for proofs
   */
  void addFormula(TNode n, bool inUnsatCore, bool inInput = true);

  /** Expand definitions in n. */
  Node expandDefinitions(TNode n,
                         NodeToNodeHashMap& cache,
                         bool expandOnly = false);

  /**
   * Simplify node "in" by expanding definitions and applying any
   * substitutions learned from preprocessing.
   */
  Node simplify(TNode in) {
    // Substitute out any abstract values in ex.
    // Expand definitions.
    NodeToNodeHashMap cache;
    Node n = expandDefinitions(in, cache).toExpr();
    // Make sure we've done all preprocessing, etc.
    Assert(d_assertions.size() == 0);
    return applySubstitutions(n).toExpr();
  }

  /**
   * Substitute away all AbstractValues in a node.
   */
  Node substituteAbstractValues(TNode n) {
    // We need to do this even if options::abstractValues() is off,
    // since the setting might have changed after we already gave out
    // some abstract values.
    return d_abstractValueMap.apply(n);
  }

  /**
   * Make a new (or return an existing) abstract value for a node.
   * Can only use this if options::abstractValues() is on.
   */
  Node mkAbstractValue(TNode n) {
    Assert(options::abstractValues());
    Node& val = d_abstractValues[n];
    if(val.isNull()) {
      val = d_smt.d_nodeManager->mkAbstractValue(n.getType());
      d_abstractValueMap.addSubstitution(val, n);
    }
    // We are supposed to ascribe types to all abstract values that go out.
    NodeManager* current = d_smt.d_nodeManager;
    Node ascription = current->mkConst(AscriptionType(n.getType().toType()));
    Node retval = current->mkNode(kind::APPLY_TYPE_ASCRIPTION, ascription, val);
    return retval;
  }

  void addUseTheoryListListener(TheoryEngine* theoryEngine){
    Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
    d_listenerRegistrations->add(
        nodeManagerOptions.registerUseTheoryListListener(
            new UseTheoryListListener(theoryEngine), true));
  }

  std::ostream* getReplayLog() const {
    return d_managedReplayLog.getReplayLog();
  }

  //------------------------------- expression names
  // implements setExpressionName, as described in smt_engine.h
  void setExpressionName(Expr e, std::string name) {
    d_exprNames[Node::fromExpr(e)] = name;
  }

  // implements getExpressionName, as described in smt_engine.h
  bool getExpressionName(Expr e, std::string& name) const {
    context::CDHashMap< Node, std::string, NodeHashFunction >::const_iterator it = d_exprNames.find(e);
    if(it!=d_exprNames.end()) {
      name = (*it).second;
      return true;
    }else{
      return false;
    }
  }
  //------------------------------- end expression names
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

SmtEngine::SmtEngine(ExprManager* em)
    : d_context(new Context()),
      d_userLevels(),
      d_userContext(new UserContext()),
      d_exprManager(em),
      d_nodeManager(d_exprManager->getNodeManager()),
      d_decisionEngine(NULL),
      d_theoryEngine(NULL),
      d_propEngine(NULL),
      d_proofManager(NULL),
      d_definedFunctions(NULL),
      d_fmfRecFunctionsDefined(NULL),
      d_assertionList(NULL),
      d_assignments(NULL),
      d_modelGlobalCommands(),
      d_modelCommands(NULL),
      d_dumpCommands(),
      d_defineCommands(),
      d_logic(),
      d_originalOptions(),
      d_pendingPops(0),
      d_fullyInited(false),
      d_problemExtended(false),
      d_queryMade(false),
      d_needPostsolve(false),
      d_earlyTheoryPP(true),
      d_globalNegation(false),
      d_status(),
      d_replayStream(NULL),
      d_private(NULL),
      d_statisticsRegistry(NULL),
      d_stats(NULL),
      d_channels(new LemmaChannels())
{
  SmtScope smts(this);
  d_originalOptions.copyValues(em->getOptions());
  d_private = new smt::SmtEnginePrivate(*this);
  d_statisticsRegistry = new StatisticsRegistry();
  d_stats = new SmtEngineStatistics();
  d_stats->d_resourceUnitsUsed.setData(
      d_private->getResourceManager()->getResourceUsage());

  // The ProofManager is constructed before any other proof objects such as
  // SatProof and TheoryProofs. The TheoryProofEngine and the SatProof are
  // initialized in TheoryEngine and PropEngine respectively.
  Assert(d_proofManager == NULL);

  // d_proofManager must be created before Options has been finished
  // being parsed from the input file. Because of this, we cannot trust
  // that options::proof() is set correctly yet.
#ifdef CVC4_PROOF
  d_proofManager = new ProofManager(d_userContext);
#endif

  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context,
                                    d_userContext,
                                    d_private->d_iteRemover,
                                    const_cast<const LogicInfo&>(d_logic),
                                    d_channels);

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(d_theoryEngine, id);
    //register with proof engine if applicable
#ifdef CVC4_PROOF
    ProofManager::currentPM()->getTheoryProofEngine()->registerTheory(d_theoryEngine->theoryOf(id));
#endif
  }

  d_private->addUseTheoryListListener(d_theoryEngine);

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_userContext->push();
  d_context->push();

  d_definedFunctions = new(true) DefinedFunctionMap(d_userContext);
  d_fmfRecFunctionsDefined = new(true) NodeList(d_userContext);
  d_modelCommands = new(true) smt::CommandList(d_userContext);
}

void SmtEngine::finishInit() {
  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  // ensure that our heuristics are properly set up
  setDefaults();

  Trace("smt-debug") << "Making decision engine..." << std::endl;

  d_decisionEngine = new DecisionEngine(d_context, d_userContext);
  d_decisionEngine->init();   // enable appropriate strategies

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  d_propEngine = new PropEngine(d_theoryEngine, d_decisionEngine, d_context,
                                d_userContext, d_private->getReplayLog(),
                                d_replayStream, d_channels);

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(d_propEngine);
  d_theoryEngine->setDecisionEngine(d_decisionEngine);
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();

  Trace("smt-debug") << "Set up assertion list..." << std::endl;
  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(options::produceAssertions() ||
     options::incrementalSolving()) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new(true) AssertionList(d_userContext);
  }

  // dump out a set-logic command
  if(Dump.isOn("benchmark")) {
    if (Dump.isOn("raw-benchmark")) {
      Dump("raw-benchmark") << SetBenchmarkLogicCommand(d_logic.getLogicString());
    } else {
      LogicInfo everything;
      everything.lock();
      Dump("benchmark") << CommentCommand("CVC4 always dumps the most general, all-supported logic (below), as some internals might require the use of a logic more general than the input.")
                        << SetBenchmarkLogicCommand(everything.getLogicString());
    }
  }

  Trace("smt-debug") << "Dump declaration commands..." << std::endl;
  // dump out any pending declaration commands
  for(unsigned i = 0; i < d_dumpCommands.size(); ++i) {
    Dump("declarations") << *d_dumpCommands[i];
    delete d_dumpCommands[i];
  }
  d_dumpCommands.clear();

  PROOF( ProofManager::currentPM()->setLogic(d_logic); );
  PROOF({
      for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
        ProofManager::currentPM()->getTheoryProofEngine()->
          finishRegisterTheory(d_theoryEngine->theoryOf(id));
      }
    });
  d_private->finishInit();
  Trace("smt-debug") << "SmtEngine::finishInit done" << std::endl;
}

void SmtEngine::finalOptionsAreSet() {
  if(d_fullyInited) {
    return;
  }

  if(! d_logic.isLocked()) {
    setLogicInternal();
  }

  // finish initialization, create the prop engine, etc.
  finishInit();

  AlwaysAssert( d_propEngine->getAssertionLevel() == 0,
                "The PropEngine has pushed but the SmtEngine "
                "hasn't finished initializing!" );

  d_fullyInited = true;
  Assert(d_logic.isLocked());

  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(true));
  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(false).notNode());
}

void SmtEngine::shutdown() {
  doPendingPops();

  while(options::incrementalSolving() && d_userContext->getLevel() > 1) {
    internalPop(true);
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  if(d_propEngine != NULL) {
    d_propEngine->shutdown();
  }
  if(d_theoryEngine != NULL) {
    d_theoryEngine->shutdown();
  }
  if(d_decisionEngine != NULL) {
    d_decisionEngine->shutdown();
  }
}

SmtEngine::~SmtEngine()
{
  SmtScope smts(this);

  try {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_context->popto(0);
    d_userContext->popto(0);

    if(d_assignments != NULL) {
      d_assignments->deleteSelf();
    }

    if(d_assertionList != NULL) {
      d_assertionList->deleteSelf();
    }

    for(unsigned i = 0; i < d_dumpCommands.size(); ++i) {
      delete d_dumpCommands[i];
      d_dumpCommands[i] = NULL;
    }
    d_dumpCommands.clear();

    DeleteAndClearCommandVector(d_modelGlobalCommands);

    if(d_modelCommands != NULL) {
      d_modelCommands->deleteSelf();
    }

    d_definedFunctions->deleteSelf();
    d_fmfRecFunctionsDefined->deleteSelf();

    //destroy all passes before destroying things that they refer to
    d_private->unregisterPreprocessingPasses();

    delete d_theoryEngine;
    d_theoryEngine = NULL;
    delete d_propEngine;
    d_propEngine = NULL;
    delete d_decisionEngine;
    d_decisionEngine = NULL;


// d_proofManager is always created when proofs are enabled at configure time.
// Becuase of this, this code should not be wrapped in PROOF() which
// additionally checks flags such as options::proof().
#ifdef CVC4_PROOF
    delete d_proofManager;
    d_proofManager = NULL;
#endif

    delete d_stats;
    d_stats = NULL;
    delete d_statisticsRegistry;
    d_statisticsRegistry = NULL;

    delete d_private;
    d_private = NULL;

    delete d_userContext;
    d_userContext = NULL;
    delete d_context;
    d_context = NULL;

    delete d_channels;
    d_channels = NULL;

  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << endl
              << e << endl;
  }
}

void SmtEngine::setLogic(const LogicInfo& logic)
{
  SmtScope smts(this);
  if(d_fullyInited) {
    throw ModalException("Cannot set logic in SmtEngine after the engine has "
                         "finished initializing.");
  }
  d_logic = logic;
  setLogicInternal();
}

void SmtEngine::setLogic(const std::string& s)
{
  SmtScope smts(this);
  try {
    setLogic(LogicInfo(s));
  } catch(IllegalArgumentException& e) {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) { setLogic(string(logic)); }
LogicInfo SmtEngine::getLogicInfo() const {
  return d_logic;
}
void SmtEngine::setFilename(std::string filename) { d_filename = filename; }
std::string SmtEngine::getFilename() const { return d_filename; }
void SmtEngine::setLogicInternal()
{
  Assert(!d_fullyInited, "setting logic in SmtEngine but the engine has already"
         " finished initializing for this run");
  d_logic.lock();
}

void SmtEngine::setDefaults() {
  Random::getRandom().setSeed(options::seed());
  // Language-based defaults
  if (!options::bitvectorDivByZeroConst.wasSetByUser())
  {
    // Bitvector-divide-by-zero changed semantics in SMT LIB 2.6, thus we
    // set this option if the input format is SMT LIB 2.6. We also set this
    // option if we are sygus, since we assume SMT LIB 2.6 semantics for sygus.
    options::bitvectorDivByZeroConst.set(
        language::isInputLang_smt2_6(options::inputLanguage())
        || options::inputLanguage() == language::input::LANG_SYGUS);
  }
  bool is_sygus = false;
  if (options::inputLanguage() == language::input::LANG_SYGUS)
  {
    is_sygus = true;
    if (!options::ceGuidedInst.wasSetByUser())
    {
      options::ceGuidedInst.set(true);
    }
    // must use Ferrante/Rackoff for real arithmetic
    if (!options::cbqiMidpoint.wasSetByUser())
    {
      options::cbqiMidpoint.set(true);
    }
    if (options::sygusRepairConst())
    {
      if (!options::cbqi.wasSetByUser())
      {
        options::cbqi.set(true);
      }
    }
  }

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER)
  {
    if (options::produceModels()
        && (d_logic.isTheoryEnabled(THEORY_ARRAYS)
            || d_logic.isTheoryEnabled(THEORY_UF)))
    {
      if (options::bitblastMode.wasSetByUser()
          || options::produceModels.wasSetByUser())
      {
        throw OptionException(std::string(
            "Eager bit-blasting currently does not support model generation "
            "for the combination of bit-vectors with arrays or uinterpreted "
            "functions. Try --bitblast=lazy"));
      }
      Notice() << "SmtEngine: setting bit-blast mode to lazy to support model"
               << "generation" << endl;
      setOption("bitblastMode", SExpr("lazy"));
    }

    if (options::incrementalSolving() && !d_logic.isPure(THEORY_BV))
    {
      throw OptionException(
          "Incremental eager bit-blasting is currently "
          "only supported for QF_BV. Try --bitblast=lazy.");
    }
  }

  if(options::forceLogicString.wasSetByUser()) {
    d_logic = LogicInfo(options::forceLogicString());
  }else if (options::solveIntAsBV() > 0) {
    d_logic = LogicInfo("QF_BV");
  }else if (d_logic.getLogicString() == "QF_NRA" && options::solveRealAsInt()) {
    d_logic = LogicInfo("QF_NIA");
  } else if ((d_logic.getLogicString() == "QF_UFBV" ||
              d_logic.getLogicString() == "QF_ABV") &&
             options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    d_logic = LogicInfo("QF_BV");
  }

  // set strings-exp
  /* - disabled for 1.4 release [MGD 2014.06.25]
  if(!d_logic.hasEverything() && d_logic.isTheoryEnabled(THEORY_STRINGS) ) {
    if(! options::stringExp.wasSetByUser()) {
      options::stringExp.set( true );
      Trace("smt") << "turning on strings-exp, for the theory of strings" << std::endl;
    }
  }
  */
  // for strings
  if(options::stringExp()) {
    if( !d_logic.isQuantified() ) {
      d_logic = d_logic.getUnlockedCopy();
      d_logic.enableQuantifiers();
      d_logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp"
                   << std::endl;
    }
    if(! options::fmfBound.wasSetByUser()) {
      options::fmfBound.set( true );
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    if(! options::fmfInstEngine.wasSetByUser()) {
      options::fmfInstEngine.set( true );
      Trace("smt") << "turning on fmf-inst-engine, for strings-exp" << std::endl;
    }
    /*
    if(! options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
      Trace("smt") << "turning on rewrite-divk, for strings-exp" << std::endl;
    }*/
    /*
    if(! options::stringFMF.wasSetByUser()) {
      options::stringFMF.set( true );
      Trace("smt") << "turning on strings-fmf, for strings-exp" << std::endl;
    }
    */
  }

  // sygus inference may require datatypes
  if (options::sygusInference())
  {
    d_logic = d_logic.getUnlockedCopy();
    d_logic.enableTheory(THEORY_DATATYPES);
    d_logic.lock();
    // since we are trying to recast as sygus, we assume the input is sygus
    is_sygus = true;
  }

  if ((options::checkModels() || options::checkSynthSol()
       || options::produceModelCores())
      && !options::produceAssertions())
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "check-models, check-synth-sol or produce-model-cores." << endl;
    setOption("produce-assertions", SExpr("true"));
  }

  // Disable options incompatible with incremental solving, unsat cores, and
  // proofs or output an error if enabled explicitly
  if (options::incrementalSolving() || options::unsatCores()
      || options::proof())
  {
    if (options::unconstrainedSimp())
    {
      if (options::unconstrainedSimp.wasSetByUser())
      {
        throw OptionException(
            "unconstrained simplification not supported with unsat "
            "cores/proofs/incremental solving");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to "
                  "support unsat cores/proofs/incremental solving"
               << endl;
      options::unconstrainedSimp.set(false);
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!options::unconstrainedSimp.wasSetByUser())
    {
      //    bool qf_sat = d_logic.isPure(THEORY_BOOL) &&
      //    !d_logic.isQuantified(); bool uncSimp = false && !qf_sat &&
      //    !options::incrementalSolving();
      bool uncSimp = !d_logic.isQuantified() && !options::produceModels()
                     && !options::produceAssignments()
                     && !options::checkModels()
                     && (d_logic.isTheoryEnabled(THEORY_ARRAYS)
                         && d_logic.isTheoryEnabled(THEORY_BV));
      Trace("smt") << "setting unconstrained simplification to " << uncSimp
                   << endl;
      options::unconstrainedSimp.set(uncSimp);
    }
  }

  // Disable options incompatible with unsat cores and proofs or output an
  // error if enabled explicitly
  if (options::unsatCores() || options::proof())
  {
    if (options::simplificationMode() != SIMPLIFICATION_MODE_NONE)
    {
      if (options::simplificationMode.wasSetByUser())
      {
        throw OptionException(
            "simplification not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat "
                  "cores/proofs"
               << endl;
      options::simplificationMode.set(SIMPLIFICATION_MODE_NONE);
    }

    if (options::pbRewrites())
    {
      if (options::pbRewrites.wasSetByUser())
      {
        throw OptionException(
            "pseudoboolean rewrites not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                  "unsat cores/proofs"
               << endl;
      setOption("pb-rewrites", false);
    }

    if (options::sortInference())
    {
      if (options::sortInference.wasSetByUser())
      {
        throw OptionException(
            "sort inference not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off sort inference to support unsat "
                  "cores/proofs"
               << endl;
      options::sortInference.set(false);
    }

    if (options::preSkolemQuant())
    {
      if (options::preSkolemQuant.wasSetByUser())
      {
        throw OptionException(
            "pre-skolemization not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support unsat "
                  "cores/proofs"
               << endl;
      options::preSkolemQuant.set(false);
    }

    if (options::bitvectorToBool())
    {
      if (options::bitvectorToBool.wasSetByUser())
      {
        throw OptionException(
            "bv-to-bool not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support unsat "
                  "cores/proofs"
               << endl;
      options::bitvectorToBool.set(false);
    }

    if (options::boolToBitvector())
    {
      if (options::boolToBitvector.wasSetByUser())
      {
        throw OptionException(
            "bool-to-bv not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support unsat "
                  "cores/proofs"
               << endl;
      options::boolToBitvector.set(false);
    }

    if (options::bvIntroducePow2())
    {
      if (options::bvIntroducePow2.wasSetByUser())
      {
        throw OptionException(
            "bv-intro-pow2 not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bv-intro-pow2 to support "
                  "unsat-cores/proofs"
               << endl;
      setOption("bv-intro-pow2", false);
    }

    if (options::repeatSimp())
    {
      if (options::repeatSimp.wasSetByUser())
      {
        throw OptionException(
            "repeat-simp not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off repeat-simp to support unsat "
                  "cores/proofs"
               << endl;
      setOption("repeat-simp", false);
    }

    if (options::globalNegate())
    {
      if (options::globalNegate.wasSetByUser())
      {
        throw OptionException(
            "global-negate not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off global-negate to support unsat "
                  "cores/proofs"
               << endl;
      setOption("global-negate", false);
    }
  }
  else
  {
    // by default, nonclausal simplification is off for QF_SAT
    if (!options::simplificationMode.wasSetByUser())
    {
      bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
      Trace("smt") << "setting simplification mode to <"
                   << d_logic.getLogicString() << "> " << (!qf_sat) << endl;
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others options::simplificationMode.set(qf_sat ||
      // quantifiers ? SIMPLIFICATION_MODE_NONE : SIMPLIFICATION_MODE_BATCH);
      options::simplificationMode.set(qf_sat ? SIMPLIFICATION_MODE_NONE
                                             : SIMPLIFICATION_MODE_BATCH);
    }
  }

  if (options::cbqiBv() && d_logic.isQuantified())
  {
    if(options::boolToBitvector.wasSetByUser()) {
      throw OptionException(
          "bool-to-bv not supported with CBQI BV for quantified logics");
    }
    Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
             << endl;
    options::boolToBitvector.set(false);
  }

  // cases where we need produce models
  if (!options::produceModels()
      && (options::produceAssignments() || options::sygusRewSynthCheck()
          || options::produceModelCores() || is_sygus))
  {
    Notice() << "SmtEngine: turning on produce-models" << endl;
    setOption("produce-models", SExpr("true"));
  }

  // Set the options for the theoryOf
  if(!options::theoryOfMode.wasSetByUser()) {
    if(d_logic.isSharingEnabled() &&
       !d_logic.isTheoryEnabled(THEORY_BV) &&
       !d_logic.isTheoryEnabled(THEORY_STRINGS) &&
       !d_logic.isTheoryEnabled(THEORY_SETS) ) {
      Trace("smt") << "setting theoryof-mode to term-based" << endl;
      options::theoryOfMode.set(THEORY_OF_TERM_BASED);
    }
  }

  // strings require LIA, UF; widen the logic
  if(d_logic.isTheoryEnabled(THEORY_STRINGS)) {
    LogicInfo log(d_logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    if(!d_logic.isTheoryEnabled(THEORY_UF)) {
      Trace("smt") << "because strings are enabled, also enabling UF" << endl;
      log.enableTheory(THEORY_UF);
    }
    if(!d_logic.isTheoryEnabled(THEORY_ARITH) || d_logic.isDifferenceLogic() || !d_logic.areIntegersUsed()) {
      Trace("smt") << "because strings are enabled, also enabling linear integer arithmetic" << endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    d_logic = log;
    d_logic.lock();
  }
  if(d_logic.isTheoryEnabled(THEORY_ARRAYS) || d_logic.isTheoryEnabled(THEORY_DATATYPES) || d_logic.isTheoryEnabled(THEORY_SETS)) {
    if(!d_logic.isTheoryEnabled(THEORY_UF)) {
      LogicInfo log(d_logic.getUnlockedCopy());
      Trace("smt") << "because a theory that permits Boolean terms is enabled, also enabling UF" << endl;
      log.enableTheory(THEORY_UF);
      d_logic = log;
      d_logic.lock();
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if(! options::ufSymmetryBreaker.wasSetByUser()) {
    bool qf_uf_noinc = d_logic.isPure(THEORY_UF) && !d_logic.isQuantified()
                       && !options::incrementalSolving() && !options::proof()
                       && !options::unsatCores();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc << endl;
    options::ufSymmetryBreaker.set(qf_uf_noinc);
  }

  // If in arrays, set the UF handler to arrays
  if(d_logic.isTheoryEnabled(THEORY_ARRAYS) && ( !d_logic.isQuantified() ||
     (d_logic.isQuantified() && !d_logic.isTheoryEnabled(THEORY_UF)))) {
    Theory::setUninterpretedSortOwner(THEORY_ARRAYS);
  } else {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  // Turn on ite simplification for QF_LIA and QF_AUFBV
  // WARNING: These checks match much more than just QF_AUFBV and
  // QF_LIA logics. --K [2014/10/15]
  if(! options::doITESimp.wasSetByUser()) {
    bool qf_aufbv = !d_logic.isQuantified() &&
      d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
      d_logic.isTheoryEnabled(THEORY_UF) &&
      d_logic.isTheoryEnabled(THEORY_BV);
    bool qf_lia = !d_logic.isQuantified() &&
      d_logic.isPure(THEORY_ARITH) &&
      d_logic.isLinear() &&
      !d_logic.isDifferenceLogic() &&
      !d_logic.areRealsUsed();

    bool iteSimp = (qf_aufbv || qf_lia);
    Trace("smt") << "setting ite simplification to " << iteSimp << endl;
    options::doITESimp.set(iteSimp);
  }
  if(! options::compressItes.wasSetByUser() ){
    bool qf_lia = !d_logic.isQuantified() &&
      d_logic.isPure(THEORY_ARITH) &&
      d_logic.isLinear() &&
      !d_logic.isDifferenceLogic() &&
      !d_logic.areRealsUsed();

    bool compressIte = qf_lia;
    Trace("smt") << "setting ite compression to " << compressIte << endl;
    options::compressItes.set(compressIte);
  }
  if(! options::simplifyWithCareEnabled.wasSetByUser() ){
    bool qf_aufbv = !d_logic.isQuantified() &&
      d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
      d_logic.isTheoryEnabled(THEORY_UF) &&
      d_logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare << endl;
    options::simplifyWithCareEnabled.set(withCare);
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if(! options::arraysEagerIndexSplitting.wasSetByUser()) {
    if (not d_logic.isQuantified() &&
        d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
        d_logic.isTheoryEnabled(THEORY_UF) &&
        d_logic.isTheoryEnabled(THEORY_ARITH)) {
      Trace("smt") << "setting array eager index splitting to false" << endl;
      options::arraysEagerIndexSplitting.set(false);
    }
  }
  // Turn on model-based arrays for QF_AX (unless models are enabled)
  // if(! options::arraysModelBased.wasSetByUser()) {
  //   if (not d_logic.isQuantified() &&
  //       d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
  //       d_logic.isPure(THEORY_ARRAYS) &&
  //       !options::produceModels() &&
  //       !options::checkModels()) {
  //     Trace("smt") << "turning on model-based array solver" << endl;
  //     options::arraysModelBased.set(true);
  //   }
  // }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if(! options::repeatSimp.wasSetByUser()) {
    bool repeatSimp = !d_logic.isQuantified() &&
                      (d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
                      d_logic.isTheoryEnabled(THEORY_UF) &&
                      d_logic.isTheoryEnabled(THEORY_BV)) &&
                      !options::unsatCores();
    Trace("smt") << "setting repeat simplification to " << repeatSimp << endl;
    options::repeatSimp.set(repeatSimp);
  }
  // Unconstrained simp currently does *not* support model generation
  if (options::unconstrainedSimp.wasSetByUser() && options::unconstrainedSimp()) {
    if (options::produceModels()) {
      if (options::produceModels.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation.");
      }
      Notice() << "SmtEngine: turning off produce-models to support unconstrainedSimp" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      if (options::produceAssignments.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation (produce-assignments).");
      }
      Notice() << "SmtEngine: turning off produce-assignments to support unconstrainedSimp" << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      if (options::checkModels.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation (check-models).");
      }
      Notice() << "SmtEngine: turning off check-models to support unconstrainedSimp" << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  if (! options::bvEagerExplanations.wasSetByUser() &&
      d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
      d_logic.isTheoryEnabled(THEORY_BV)) {
    Trace("smt") << "enabling eager bit-vector explanations " << endl;
    options::bvEagerExplanations.set(true);
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if(! options::arithRewriteEq.wasSetByUser()) {
    bool arithRewriteEq = d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq << endl;
    options::arithRewriteEq.set(arithRewriteEq);
  }
  if(!  options::arithHeuristicPivots.wasSetByUser()) {
    int16_t heuristicPivots = 5;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()) {
      if(d_logic.isDifferenceLogic()) {
        heuristicPivots = -1;
      } else if(!d_logic.areIntegersUsed()) {
        heuristicPivots = 0;
      }
    }
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots << endl;
    options::arithHeuristicPivots.set(heuristicPivots);
  }
  if(! options::arithPivotThreshold.wasSetByUser()){
    uint16_t pivotThreshold = 2;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      if(d_logic.isDifferenceLogic()){
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold << endl;
    options::arithPivotThreshold.set(pivotThreshold);
  }
  if(! options::arithStandardCheckVarOrderPivots.wasSetByUser()){
    int16_t varOrderPivots = -1;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  " << varOrderPivots << endl;
    options::arithStandardCheckVarOrderPivots.set(varOrderPivots);
  }
  // Turn off early theory preprocessing if arithRewriteEq is on
  if (options::arithRewriteEq()) {
    d_earlyTheoryPP = false;
  }
  if (d_logic.isPure(THEORY_ARITH) && !d_logic.areRealsUsed())
  {
    if (!options::nlExtTangentPlanesInterleave.wasSetByUser())
    {
      Trace("smt") << "setting nlExtTangentPlanesInterleave to true" << endl;
      options::nlExtTangentPlanesInterleave.set(true);
    }
  }

  // Set decision mode based on logic (if not set by user)
  if(!options::decisionMode.wasSetByUser()) {
    decision::DecisionMode decMode =
      // ALL
      d_logic.hasEverything() ? decision::DECISION_STRATEGY_JUSTIFICATION :
      ( // QF_BV
        (not d_logic.isQuantified() &&
          d_logic.isPure(THEORY_BV)
          ) ||
        // QF_AUFBV or QF_ABV or QF_UFBV
        (not d_logic.isQuantified() &&
         (d_logic.isTheoryEnabled(THEORY_ARRAYS) ||
          d_logic.isTheoryEnabled(THEORY_UF)) &&
         d_logic.isTheoryEnabled(THEORY_BV)
         ) ||
        // QF_AUFLIA (and may be ends up enabling QF_AUFLRA?)
        (not d_logic.isQuantified() &&
         d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
         d_logic.isTheoryEnabled(THEORY_UF) &&
         d_logic.isTheoryEnabled(THEORY_ARITH)
         ) ||
        // QF_LRA
        (not d_logic.isQuantified() &&
         d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
         ) ||
        // Quantifiers
        d_logic.isQuantified() ||
        // Strings
        d_logic.isTheoryEnabled(THEORY_STRINGS)
        ? decision::DECISION_STRATEGY_JUSTIFICATION
        : decision::DECISION_STRATEGY_INTERNAL
      );

    bool stoponly =
      // ALL
      d_logic.hasEverything() || d_logic.isTheoryEnabled(THEORY_STRINGS) ? false :
      ( // QF_AUFLIA
        (not d_logic.isQuantified() &&
         d_logic.isTheoryEnabled(THEORY_ARRAYS) &&
         d_logic.isTheoryEnabled(THEORY_UF) &&
         d_logic.isTheoryEnabled(THEORY_ARITH)
         ) ||
        // QF_LRA
        (not d_logic.isQuantified() &&
         d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
         )
        ? true : false
      );

    Trace("smt") << "setting decision mode to " << decMode << endl;
    options::decisionMode.set(decMode);
    options::decisionStopOnly.set(stoponly);
  }
  if( options::incrementalSolving() ){
    //disable modes not supported by incremental
    options::sortInference.set( false );
    options::ufssFairnessMonotone.set( false );
    options::quantEpr.set( false );
    options::globalNegate.set(false);
  }
  if( d_logic.hasCardinalityConstraints() ){
    //must have finite model finding on
    options::finiteModelFind.set( true );
  }

  //if it contains a theory with non-termination, do not strictly enforce that quantifiers and theory combination must be interleaved
  if( d_logic.isTheoryEnabled(THEORY_STRINGS) || (d_logic.isTheoryEnabled(THEORY_ARITH) && !d_logic.isLinear()) ){
    if( !options::instWhenStrictInterleave.wasSetByUser() ){
      options::instWhenStrictInterleave.set( false );
    }
  }

  //local theory extensions
  if( options::localTheoryExt() ){
    if( !options::instMaxLevel.wasSetByUser() ){
      options::instMaxLevel.set( 0 );
    }
  }
  if( options::instMaxLevel()!=-1 ){
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel" << endl;
    options::cbqi.set(false);
  }
  //track instantiations?
  if( options::cbqiNestedQE() || ( options::proof() && !options::trackInstLemmas.wasSetByUser() ) ){
    options::trackInstLemmas.set( true );
  }

  if( ( options::fmfBoundLazy.wasSetByUser() && options::fmfBoundLazy() ) ||
      ( options::fmfBoundInt.wasSetByUser() && options::fmfBoundInt() ) ) {
    options::fmfBound.set( true );
  }
  //now have determined whether fmfBoundInt is on/off
  //apply fmfBoundInt options
  if( options::fmfBound() ){
    //must have finite model finding on
    options::finiteModelFind.set( true );
    if (!options::mbqiMode.wasSetByUser()
        || (options::mbqiMode() != quantifiers::MBQI_NONE
            && options::mbqiMode() != quantifiers::MBQI_FMC))
    {
      //if bounded integers are set, use no MBQI by default
      options::mbqiMode.set( quantifiers::MBQI_NONE );
    }
    if( ! options::prenexQuant.wasSetByUser() ){
      options::prenexQuant.set( quantifiers::PRENEX_QUANT_NONE );
    }
  }
  if( options::ufHo() ){
    //if higher-order, then current variants of model-based instantiation cannot be used
    if( options::mbqiMode()!=quantifiers::MBQI_NONE ){
      options::mbqiMode.set( quantifiers::MBQI_NONE );
    }
  }
  if( options::mbqiMode()==quantifiers::MBQI_ABS ){
    if( !d_logic.isPure(THEORY_UF) ){
      //MBQI_ABS is only supported in pure quantified UF
      options::mbqiMode.set( quantifiers::MBQI_FMC );
    }
  }
  if( options::fmfFunWellDefinedRelevant() ){
    if( !options::fmfFunWellDefined.wasSetByUser() ){
      options::fmfFunWellDefined.set( true );
    }
  }
  if( options::fmfFunWellDefined() ){
    if( !options::finiteModelFind.wasSetByUser() ){
      options::finiteModelFind.set( true );
    }
  }
  //EPR
  if( options::quantEpr() ){
    if( !options::preSkolemQuant.wasSetByUser() ){
      options::preSkolemQuant.set( true );
    }
  }

  //now, have determined whether finite model find is on/off
  //apply finite model finding options
  if( options::finiteModelFind() ){
    //apply conservative quantifiers splitting
    if( !options::quantDynamicSplit.wasSetByUser() ){
      options::quantDynamicSplit.set( quantifiers::QUANT_DSPLIT_MODE_DEFAULT );
    }
    //do not eliminate extended arithmetic symbols from quantified formulas
    if( !options::elimExtArithQuant.wasSetByUser() ){
      options::elimExtArithQuant.set( false );
    }
    if( !options::eMatching.wasSetByUser() ){
      options::eMatching.set( options::fmfInstEngine() );
    }
    if( !options::instWhenMode.wasSetByUser() ){
      //instantiate only on last call
      if( options::eMatching() ){
        options::instWhenMode.set( quantifiers::INST_WHEN_LAST_CALL );
      }
    }
    if( options::mbqiMode()==quantifiers::MBQI_ABS ){
      if( !options::preSkolemQuant.wasSetByUser() ){
        options::preSkolemQuant.set( true );
      }
      if( !options::preSkolemQuantNested.wasSetByUser() ){
        options::preSkolemQuantNested.set( true );
      }
      if( !options::fmfOneInstPerRound.wasSetByUser() ){
        options::fmfOneInstPerRound.set( true );
      }
    }
  }

  //apply counterexample guided instantiation options
  // if we are attempting to rewrite everything to SyGuS, use ceGuidedInst
  if (options::sygusInference())
  {
    if (!options::ceGuidedInst.wasSetByUser())
    {
      options::ceGuidedInst.set(true);
    }
    // optimization: apply preskolemization, makes it succeed more often
    if (!options::preSkolemQuant.wasSetByUser())
    {
      options::preSkolemQuant.set(true);
    }
    if (!options::preSkolemQuantNested.wasSetByUser())
    {
      options::preSkolemQuantNested.set(true);
    }
  }
  if( options::cegqiSingleInvMode()!=quantifiers::CEGQI_SI_MODE_NONE ){
    if( !options::ceGuidedInst.wasSetByUser() ){
      options::ceGuidedInst.set( true );
    }
  }
  // if sygus is enabled, set the defaults for sygus
  if( options::ceGuidedInst() ){
    //counterexample-guided instantiation for sygus
    if( !options::cegqiSingleInvMode.wasSetByUser() ){
      options::cegqiSingleInvMode.set( quantifiers::CEGQI_SI_MODE_USE );
    }
    if( !options::quantConflictFind.wasSetByUser() ){
      options::quantConflictFind.set( false );
    }
    if( !options::instNoEntail.wasSetByUser() ){
      options::instNoEntail.set( false );
    }
    if (!options::cbqiFullEffort.wasSetByUser())
    {
      // should use full effort cbqi for single invocation and repair const
      options::cbqiFullEffort.set(true);
    }
    if (options::sygusRew())
    {
      options::sygusRewSynth.set(true);
      options::sygusRewVerify.set(true);
    }
    if (options::sygusRewSynth() || options::sygusRewVerify())
    {
      // rewrite rule synthesis implies that sygus stream must be true
      options::sygusStream.set(true);
    }
    if (options::sygusStream())
    {
      // PBE and streaming modes are incompatible
      if (!options::sygusSymBreakPbe.wasSetByUser())
      {
        options::sygusSymBreakPbe.set(false);
      }
      if (!options::sygusUnifPbe.wasSetByUser())
      {
        options::sygusUnifPbe.set(false);
      }
    }
    //do not allow partial functions
    if( !options::bitvectorDivByZeroConst.wasSetByUser() ){
      options::bitvectorDivByZeroConst.set( true );
    }
    if( !options::dtRewriteErrorSel.wasSetByUser() ){
      options::dtRewriteErrorSel.set( true );
    }
    //do not miniscope
    if( !options::miniscopeQuant.wasSetByUser() ){
      options::miniscopeQuant.set( false );
    }
    if( !options::miniscopeQuantFreeVar.wasSetByUser() ){
      options::miniscopeQuantFreeVar.set( false );
    }
    if (!options::quantSplit.wasSetByUser())
    {
      options::quantSplit.set(false);
    }
    //rewrite divk
    if( !options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
    }
    //do not do macros
    if( !options::macrosQuant.wasSetByUser()) {
      options::macrosQuant.set( false );
    }
    if( !options::cbqiPreRegInst.wasSetByUser()) {
      options::cbqiPreRegInst.set( true );
    }
  }
  //counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if (d_logic.isQuantified()
      && ((options::decisionMode() != decision::DECISION_STRATEGY_INTERNAL
           && (d_logic.isTheoryEnabled(THEORY_ARITH)
               || d_logic.isTheoryEnabled(THEORY_DATATYPES)
               || d_logic.isTheoryEnabled(THEORY_BV)
               || d_logic.isTheoryEnabled(THEORY_FP)))
          || d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV)
          || options::cbqiAll()))
  {
    if( !options::cbqi.wasSetByUser() ){
      options::cbqi.set( true );
    }
    // check whether we should apply full cbqi
    if (d_logic.isPure(THEORY_BV))
    {
      if (!options::cbqiFullEffort.wasSetByUser())
      {
        options::cbqiFullEffort.set(true);
      }
    }
  }
  if( options::cbqi() ){
    //must rewrite divk
    if( !options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
    }
    if (options::incrementalSolving())
    {
      // cannot do nested quantifier elimination in incremental mode
      options::cbqiNestedQE.set(false);
    }
    if (d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV))
    {
      if( !options::quantConflictFind.wasSetByUser() ){
        options::quantConflictFind.set( false );
      }
      if( !options::instNoEntail.wasSetByUser() ){
        options::instNoEntail.set( false );
      }
      if( !options::instWhenMode.wasSetByUser() && options::cbqiModel() ){
        //only instantiation should happen at last call when model is avaiable
        options::instWhenMode.set( quantifiers::INST_WHEN_LAST_CALL );
      }
    }else{
      // only supported in pure arithmetic or pure BV
      options::cbqiNestedQE.set(false);
    }
    // prenexing
    if (options::cbqiNestedQE()
        || options::decisionMode() == decision::DECISION_STRATEGY_INTERNAL)
    {
      // only complete with prenex = disj_normal or normal
      if (options::prenexQuant() <= quantifiers::PRENEX_QUANT_DISJ_NORMAL)
      {
        options::prenexQuant.set(quantifiers::PRENEX_QUANT_DISJ_NORMAL);
      }
    }
    else if (options::globalNegate())
    {
      if (!options::prenexQuant.wasSetByUser())
      {
        options::prenexQuant.set(quantifiers::PRENEX_QUANT_NONE);
      }
    }
  }
  //implied options...
  if( options::strictTriggers() ){
    if( !options::userPatternsQuant.wasSetByUser() ){
      options::userPatternsQuant.set( quantifiers::USER_PAT_MODE_TRUST );
    }
  }
  if( options::qcfMode.wasSetByUser() || options::qcfTConstraint() ){
    options::quantConflictFind.set( true );
  }
  if( options::cbqiNestedQE() ){
    options::prenexQuantUser.set( true );
    if( !options::preSkolemQuant.wasSetByUser() ){
      options::preSkolemQuant.set( true );
    }
  }
  //for induction techniques
  if( options::quantInduction() ){
    if( !options::dtStcInduction.wasSetByUser() ){
      options::dtStcInduction.set( true );
    }
    if( !options::intWfInduction.wasSetByUser() ){
      options::intWfInduction.set( true );
    }
  }
  if( options::dtStcInduction() ){
    //try to remove ITEs from quantified formulas
    if( !options::iteDtTesterSplitQuant.wasSetByUser() ){
      options::iteDtTesterSplitQuant.set( true );
    }
    if( !options::iteLiftQuant.wasSetByUser() ){
      options::iteLiftQuant.set( quantifiers::ITE_LIFT_QUANT_MODE_ALL );
    }
  }
  if( options::intWfInduction() ){
    if( !options::purifyTriggers.wasSetByUser() ){
      options::purifyTriggers.set( true );
    }
  }
  if( options::conjectureNoFilter() ){
    if( !options::conjectureFilterActiveTerms.wasSetByUser() ){
      options::conjectureFilterActiveTerms.set( false );
    }
    if( !options::conjectureFilterCanonical.wasSetByUser() ){
      options::conjectureFilterCanonical.set( false );
    }
    if( !options::conjectureFilterModel.wasSetByUser() ){
      options::conjectureFilterModel.set( false );
    }
  }
  if( options::conjectureGenPerRound.wasSetByUser() ){
    if( options::conjectureGenPerRound()>0 ){
      options::conjectureGen.set( true );
    }else{
      options::conjectureGen.set( false );
    }
  }
  //can't pre-skolemize nested quantifiers without UF theory
  if( !d_logic.isTheoryEnabled(THEORY_UF) && options::preSkolemQuant() ){
    if( !options::preSkolemQuantNested.wasSetByUser() ){
      options::preSkolemQuantNested.set( false );
    }
  }
  if( !d_logic.isTheoryEnabled(THEORY_DATATYPES) ){
    options::quantDynamicSplit.set( quantifiers::QUANT_DSPLIT_MODE_NONE );
  }

  //until bugs 371,431 are fixed
  if( ! options::minisatUseElim.wasSetByUser()){
    // cannot use minisat elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (d_logic.isTheoryEnabled(THEORY_SETS) || d_logic.isQuantified()
        || options::produceModels() || options::produceAssignments()
        || options::checkModels()
        || (d_logic.isTheoryEnabled(THEORY_ARITH) && !d_logic.isLinear()))
    {
      options::minisatUseElim.set( false );
    }
  }
  else if (options::minisatUseElim()) {
    if (options::produceModels()) {
      Notice() << "SmtEngine: turning off produce-models to support minisatUseElim" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      Notice() << "SmtEngine: turning off produce-assignments to support minisatUseElim" << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      Notice() << "SmtEngine: turning off check-models to support minisatUseElim" << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments() || options::checkModels()) {
    options::arraysOptimizeLinear.set(false);
    options::arraysLazyRIntro1.set(false);
  }

  // Non-linear arithmetic does not support models unless nlExt is enabled
  if ((d_logic.isTheoryEnabled(THEORY_ARITH) && !d_logic.isLinear()
       && !options::nlExt())
      || options::globalNegate())
  {
    std::string reason =
        options::globalNegate() ? "--global-negate" : "nonlinear arithmetic";
    if (options::produceModels()) {
      if(options::produceModels.wasSetByUser()) {
        throw OptionException(
            std::string("produce-model not supported with " + reason));
      }
      Warning()
          << "SmtEngine: turning off produce-models because unsupported for "
          << reason << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      if(options::produceAssignments.wasSetByUser()) {
        throw OptionException(
            std::string("produce-assignments not supported with " + reason));
      }
      Warning() << "SmtEngine: turning off produce-assignments because "
                   "unsupported for "
                << reason << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      if(options::checkModels.wasSetByUser()) {
        throw OptionException(
            std::string("check-models not supported with " + reason));
      }
      Warning()
          << "SmtEngine: turning off check-models because unsupported for "
          << reason << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  if(options::incrementalSolving() && options::proof()) {
    Warning() << "SmtEngine: turning off incremental solving mode (not yet supported with --proof, try --tear-down-incremental instead)" << endl;
    setOption("incremental", SExpr("false"));
  }

  if (options::proof())
  {
    if (options::bitvectorAlgebraicSolver())
    {
      if (options::bitvectorAlgebraicSolver.wasSetByUser())
      {
        throw OptionException(
            "--bv-algebraic-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv algebraic solver to support proofs"
               << std::endl;
      options::bitvectorAlgebraicSolver.set(false);
    }
    if (options::bitvectorEqualitySolver())
    {
      if (options::bitvectorEqualitySolver.wasSetByUser())
      {
        throw OptionException("--bv-eq-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv eq solver to support proofs"
               << std::endl;
      options::bitvectorEqualitySolver.set(false);
    }
    if (options::bitvectorInequalitySolver())
    {
      if (options::bitvectorInequalitySolver.wasSetByUser())
      {
        throw OptionException(
            "--bv-inequality-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv ineq solver to support proofs"
               << std::endl;
      options::bitvectorInequalitySolver.set(false);
    }
  }

  if (!options::bitvectorEqualitySolver())
  {
    if (options::bvLazyRewriteExtf())
    {
      if (options::bvLazyRewriteExtf.wasSetByUser())
      {
        throw OptionException(
            "--bv-lazy-rewrite-extf requires --bv-eq-solver to be set");
      }
    }
    Trace("smt")
        << "disabling bvLazyRewriteExtf since equality solver is disabled"
        << endl;
    options::bvLazyRewriteExtf.set(false);
  }
}

void SmtEngine::setProblemExtended(bool value)
{
  d_problemExtended = value;
  if (value) { d_assumptions.clear(); }
}

void SmtEngine::setInfo(const std::string& key, const CVC4::SExpr& value)
{
  SmtScope smts(this);

  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    if(key == "status") {
      string s = value.getValue();
      BenchmarkStatus status =
        (s == "sat") ? SMT_SATISFIABLE :
          ((s == "unsat") ? SMT_UNSATISFIABLE : SMT_UNKNOWN);
      Dump("benchmark") << SetBenchmarkStatusCommand(status);
    } else {
      Dump("benchmark") << SetInfoCommand(key, value);
    }
  }

  // Check for CVC4-specific info keys (prefixed with "cvc4-" or "cvc4_")
  if(key.length() > 5) {
    string prefix = key.substr(0, 5);
    if(prefix == "cvc4-" || prefix == "cvc4_") {
      string cvc4key = key.substr(5);
      if(cvc4key == "logic") {
        if(! value.isAtom()) {
          throw OptionException("argument to (set-info :cvc4-logic ..) must be a string");
        }
        SmtScope smts(this);
        d_logic = value.getValue();
        setLogicInternal();
        return;
      } else {
        throw UnrecognizedOptionException();
      }
    }
  }

  // Check for standard info keys (SMT-LIB v1, SMT-LIB v2, ...)
  if (key == "source" || key == "category" || key == "difficulty"
      || key == "notes" || key == "name" || key == "license")
  {
    // ignore these
    return;
  }
  else if (key == "filename")
  {
    d_filename = value.getValue();
    return;
  }
  else if (key == "smt-lib-version" && !options::inputLanguage.wasSetByUser())
  {
    language::input::Language ilang = language::input::LANG_AUTO;
    if( (value.isInteger() && value.getIntegerValue() == Integer(2)) ||
        (value.isRational() && value.getRationalValue() == Rational(2)) ||
        value.getValue() == "2" ||
        value.getValue() == "2.0" ) {
      ilang = language::input::LANG_SMTLIB_V2_0;
    } else if( (value.isRational() && value.getRationalValue() == Rational(5, 2)) ||
               value.getValue() == "2.5" ) {
      ilang = language::input::LANG_SMTLIB_V2_5;
    } else if( (value.isRational() && value.getRationalValue() == Rational(13, 5)) ||
               value.getValue() == "2.6" ) {
      ilang = language::input::LANG_SMTLIB_V2_6;
    }
    else if (value.getValue() == "2.6.1")
    {
      ilang = language::input::LANG_SMTLIB_V2_6_1;
    }
    else
    {
      Warning() << "Warning: unsupported smt-lib-version: " << value << endl;
      throw UnrecognizedOptionException();
    }
    options::inputLanguage.set(ilang);
    // also update the output language
    if (!options::outputLanguage.wasSetByUser())
    {
      language::output::Language olang = language::toOutputLanguage(ilang);
      if (options::outputLanguage() != olang)
      {
        options::outputLanguage.set(olang);
        *options::out() << language::SetLanguage(olang);
      }
    }
    return;
  } else if(key == "status") {
    string s;
    if(value.isAtom()) {
      s = value.getValue();
    }
    if(s != "sat" && s != "unsat" && s != "unknown") {
      throw OptionException("argument to (set-info :status ..) must be "
                            "`sat' or `unsat' or `unknown'");
    }
    d_status = Result(s, d_filename);
    return;
  }
  throw UnrecognizedOptionException();
}

CVC4::SExpr SmtEngine::getInfo(const std::string& key) const {

  SmtScope smts(this);

  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if(key == "all-statistics") {
    vector<SExpr> stats;
    for(StatisticsRegistry::const_iterator i = NodeManager::fromExprManager(d_exprManager)->getStatisticsRegistry()->begin();
        i != NodeManager::fromExprManager(d_exprManager)->getStatisticsRegistry()->end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    for(StatisticsRegistry::const_iterator i = d_statisticsRegistry->begin();
        i != d_statisticsRegistry->end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    return SExpr(stats);
  } else if(key == "error-behavior") {
    // immediate-exit | continued-execution
    if( options::continuedExecution() || options::interactive() ) {
      return SExpr(SExpr::Keyword("continued-execution"));
    } else {
      return SExpr(SExpr::Keyword("immediate-exit"));
    }
  } else if(key == "name") {
    return SExpr(Configuration::getName());
  } else if(key == "version") {
    return SExpr(Configuration::getVersionString());
  } else if(key == "authors") {
    return SExpr(Configuration::about());
  } else if(key == "status") {
    // sat | unsat | unknown
    switch(d_status.asSatisfiabilityResult().isSat()) {
    case Result::SAT:
      return SExpr(SExpr::Keyword("sat"));
    case Result::UNSAT:
      return SExpr(SExpr::Keyword("unsat"));
    default:
      return SExpr(SExpr::Keyword("unknown"));
    }
  } else if(key == "reason-unknown") {
    if(!d_status.isNull() && d_status.isUnknown()) {
      stringstream ss;
      ss << d_status.whyUnknown();
      string s = ss.str();
      transform(s.begin(), s.end(), s.begin(), ::tolower);
      return SExpr(SExpr::Keyword(s));
    } else {
      throw ModalException("Can't get-info :reason-unknown when the "
                           "last result wasn't unknown!");
    }
  } else if(key == "assertion-stack-levels") {
    AlwaysAssert(d_userLevels.size() <=
                 std::numeric_limits<unsigned long int>::max());
    return SExpr(static_cast<unsigned long int>(d_userLevels.size()));
  } else if(key == "all-options") {
    // get the options, like all-statistics
    std::vector< std::vector<std::string> > current_options =
      Options::current()->getOptions();
    return SExpr::parseListOfListOfAtoms(current_options);
  } else {
    throw UnrecognizedOptionException();
  }
}

void SmtEngine::debugCheckFormals(const std::vector<Expr>& formals, Expr func)
{
  for(std::vector<Expr>::const_iterator i = formals.begin(); i != formals.end(); ++i) {
    if((*i).getKind() != kind::BOUND_VARIABLE) {
      stringstream ss;
      ss << "All formal arguments to defined functions must be BOUND_VARIABLEs, but in the\n"
         << "definition of function " << func << ", formal\n"
         << "  " << *i << "\n"
         << "has kind " << (*i).getKind();
      throw TypeCheckingException(func, ss.str());
    }
  }
}

void SmtEngine::debugCheckFunctionBody(Expr formula,
                                       const std::vector<Expr>& formals,
                                       Expr func)
{
  Type formulaType = formula.getType(options::typeChecking());
  Type funcType = func.getType();
  // We distinguish here between definitions of constants and functions,
  // because the type checking for them is subtly different.  Perhaps we
  // should instead have SmtEngine::defineFunction() and
  // SmtEngine::defineConstant() for better clarity, although then that
  // doesn't match the SMT-LIBv2 standard...
  if(formals.size() > 0) {
    Type rangeType = FunctionType(funcType).getRangeType();
    if(! formulaType.isComparableTo(rangeType)) {
      stringstream ss;
      ss << "Type of defined function does not match its declaration\n"
         << "The function  : " << func << "\n"
         << "Declared type : " << rangeType << "\n"
         << "The body      : " << formula << "\n"
         << "Body type     : " << formulaType;
      throw TypeCheckingException(func, ss.str());
    }
  } else {
    if(! formulaType.isComparableTo(funcType)) {
      stringstream ss;
      ss << "Declared type of defined constant does not match its definition\n"
         << "The constant   : " << func << "\n"
         << "Declared type  : " << funcType << " " << Type::getTypeNode(funcType)->getId() << "\n"
         << "The definition : " << formula << "\n"
         << "Definition type: " << formulaType << " " << Type::getTypeNode(formulaType)->getId();
      throw TypeCheckingException(func, ss.str());
    }
  }
}

void SmtEngine::defineFunction(Expr func,
                               const std::vector<Expr>& formals,
                               Expr formula)
{
  SmtScope smts(this);
  doPendingPops();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  stringstream ss;
  ss << language::SetLanguage(
            language::SetLanguage::getLanguage(Dump.getStream()))
     << func;
  DefineFunctionCommand c(ss.str(), func, formals, formula);
  addToModelCommandAndDump(
      c, ExprManager::VAR_FLAG_DEFINED, true, "declarations");

  PROOF(if (options::checkUnsatCores()) {
    d_defineCommands.push_back(c.clone());
  });

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  // Substitute out any abstract values in formula
  Expr form =
      d_private->substituteAbstractValues(Node::fromExpr(formula)).toExpr();

  TNode funcNode = func.getTNode();
  vector<Node> formalsNodes;
  for(vector<Expr>::const_iterator i = formals.begin(),
        iend = formals.end();
      i != iend;
      ++i) {
    formalsNodes.push_back((*i).getNode());
  }
  TNode formNode = form.getTNode();
  DefinedFunction def(funcNode, formalsNodes, formNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  Debug("smt") << "definedFunctions insert " << funcNode << " " << formNode << endl;
  d_definedFunctions->insert(funcNode, def);
}

void SmtEngine::defineFunctionsRec(
    const std::vector<Expr>& funcs,
    const std::vector<std::vector<Expr> >& formals,
    const std::vector<Expr>& formulas)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT defineFunctionsRec(...)" << endl;

  if (funcs.size() != formals.size() && funcs.size() != formulas.size())
  {
    stringstream ss;
    ss << "Number of functions, formals, and function bodies passed to "
          "defineFunctionsRec do not match:"
       << "\n"
       << "        #functions : " << funcs.size() << "\n"
       << "        #arg lists : " << formals.size() << "\n"
       << "  #function bodies : " << formulas.size() << "\n";
    throw ModalException(ss.str());
  }
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    // check formal argument list
    debugCheckFormals(formals[i], funcs[i]);
    // type check body
    debugCheckFunctionBody(formulas[i], formals[i], funcs[i]);
  }

  if (Dump.isOn("raw-benchmark"))
  {
    Dump("raw-benchmark") << DefineFunctionRecCommand(funcs, formals, formulas);
  }

  ExprManager* em = getExprManager();
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    // we assert a quantified formula
    Expr func_app;
    // make the function application
    if (formals[i].empty())
    {
      // it has no arguments
      func_app = funcs[i];
    }
    else
    {
      std::vector<Expr> children;
      children.push_back(funcs[i]);
      children.insert(children.end(), formals[i].begin(), formals[i].end());
      func_app = em->mkExpr(kind::APPLY_UF, children);
    }
    Expr lem = em->mkExpr(kind::EQUAL, func_app, formulas[i]);
    if (!formals[i].empty())
    {
      // set the attribute to denote this is a function definition
      std::string attr_name("fun-def");
      Expr aexpr = em->mkExpr(kind::INST_ATTRIBUTE, func_app);
      aexpr = em->mkExpr(kind::INST_PATTERN_LIST, aexpr);
      std::vector<Expr> expr_values;
      std::string str_value;
      setUserAttribute(attr_name, func_app, expr_values, str_value);
      // make the quantified formula
      Expr boundVars = em->mkExpr(kind::BOUND_VAR_LIST, formals[i]);
      lem = em->mkExpr(kind::FORALL, boundVars, lem, aexpr);
    }
    // assert the quantified formula
    //   notice we don't call assertFormula directly, since this would
    //   duplicate the output on raw-benchmark.
    Expr e = d_private->substituteAbstractValues(Node::fromExpr(lem)).toExpr();
    if (d_assertionList != NULL)
    {
      d_assertionList->push_back(e);
    }
    d_private->addFormula(e.getNode(), false);
  }
}

void SmtEngine::defineFunctionRec(Expr func,
                                  const std::vector<Expr>& formals,
                                  Expr formula)
{
  std::vector<Expr> funcs;
  funcs.push_back(func);
  std::vector<std::vector<Expr> > formals_multi;
  formals_multi.push_back(formals);
  std::vector<Expr> formulas;
  formulas.push_back(formula);
  defineFunctionsRec(funcs, formals_multi, formulas);
}

bool SmtEngine::isDefinedFunction( Expr func ){
  Node nf = Node::fromExpr( func );
  Debug("smt") << "isDefined function " << nf << "?" << std::endl;
  return d_definedFunctions->find(nf) != d_definedFunctions->end();
}

void SmtEnginePrivate::finishInit()
{
  d_preprocessingPassContext.reset(new PreprocessingPassContext(
      &d_smt, d_resourceManager, &d_iteRemover, &d_propagator));
  // TODO: register passes here (this will likely change when we add support for
  // actually assembling preprocessing pipelines).
  std::unique_ptr<ApplySubsts> applySubsts(
      new ApplySubsts(d_preprocessingPassContext.get()));
  std::unique_ptr<ApplyToConst> applyToConst(
      new ApplyToConst(d_preprocessingPassContext.get()));
  std::unique_ptr<BoolToBV> boolToBv(
      new BoolToBV(d_preprocessingPassContext.get()));
  std::unique_ptr<BvAbstraction> bvAbstract(
      new BvAbstraction(d_preprocessingPassContext.get()));
  std::unique_ptr<BvEagerAtoms> bvEagerAtoms(
      new BvEagerAtoms(d_preprocessingPassContext.get()));
  std::unique_ptr<BVAckermann> bvAckermann(
      new BVAckermann(d_preprocessingPassContext.get()));
  std::unique_ptr<BVGauss> bvGauss(
      new BVGauss(d_preprocessingPassContext.get()));
  std::unique_ptr<BvIntroPow2> bvIntroPow2(
      new BvIntroPow2(d_preprocessingPassContext.get()));
  std::unique_ptr<BVToBool> bvToBool(
      new BVToBool(d_preprocessingPassContext.get()));
  std::unique_ptr<ExtRewPre> extRewPre(
      new ExtRewPre(d_preprocessingPassContext.get()));
  std::unique_ptr<GlobalNegate> globalNegate(
      new GlobalNegate(d_preprocessingPassContext.get()));
  std::unique_ptr<IntToBV> intToBV(
      new IntToBV(d_preprocessingPassContext.get()));
  std::unique_ptr<ITESimp> iteSimp(
      new ITESimp(d_preprocessingPassContext.get()));
  std::unique_ptr<NlExtPurify> nlExtPurify(
      new NlExtPurify(d_preprocessingPassContext.get()));
  std::unique_ptr<NonClausalSimp> nonClausalSimp(
      new NonClausalSimp(d_preprocessingPassContext.get()));
  std::unique_ptr<MipLibTrick> mipLibTrick(
      new MipLibTrick(d_preprocessingPassContext.get()));
  std::unique_ptr<QuantifiersPreprocess> quantifiersPreprocess(
      new QuantifiersPreprocess(d_preprocessingPassContext.get()));
  std::unique_ptr<PseudoBooleanProcessor> pbProc(
      new PseudoBooleanProcessor(d_preprocessingPassContext.get()));
  std::unique_ptr<IteRemoval> iteRemoval(
      new IteRemoval(d_preprocessingPassContext.get()));
  std::unique_ptr<RealToInt> realToInt(
      new RealToInt(d_preprocessingPassContext.get()));
  std::unique_ptr<Rewrite> rewrite(
      new Rewrite(d_preprocessingPassContext.get()));
  std::unique_ptr<SortInferencePass> sortInfer(
      new SortInferencePass(d_preprocessingPassContext.get(),
                            d_smt.d_theoryEngine->getSortInference()));
  std::unique_ptr<StaticLearning> staticLearning(
      new StaticLearning(d_preprocessingPassContext.get()));
  std::unique_ptr<SygusInference> sygusInfer(
      new SygusInference(d_preprocessingPassContext.get()));
  std::unique_ptr<SymBreakerPass> sbProc(
      new SymBreakerPass(d_preprocessingPassContext.get()));
  std::unique_ptr<SynthRewRulesPass> srrProc(
      new SynthRewRulesPass(d_preprocessingPassContext.get()));
  std::unique_ptr<SepSkolemEmp> sepSkolemEmp(
      new SepSkolemEmp(d_preprocessingPassContext.get()));
  std::unique_ptr<TheoryPreprocess> theoryPreprocess(
      new TheoryPreprocess(d_preprocessingPassContext.get()));
  std::unique_ptr<UnconstrainedSimplifier> unconstrainedSimplifier(
      new UnconstrainedSimplifier(d_preprocessingPassContext.get()));
  d_preprocessingPassRegistry.registerPass("apply-substs",
                                           std::move(applySubsts));
  d_preprocessingPassRegistry.registerPass("apply-to-const",
                                           std::move(applyToConst));
  d_preprocessingPassRegistry.registerPass("bool-to-bv", std::move(boolToBv));
  d_preprocessingPassRegistry.registerPass("bv-abstraction",
                                           std::move(bvAbstract));
  d_preprocessingPassRegistry.registerPass("bv-ackermann",
                                           std::move(bvAckermann));
  d_preprocessingPassRegistry.registerPass("bv-eager-atoms",
                                           std::move(bvEagerAtoms));
  std::unique_ptr<QuantifierMacros> quantifierMacros(
      new QuantifierMacros(d_preprocessingPassContext.get()));
  d_preprocessingPassRegistry.registerPass("bv-gauss", std::move(bvGauss));
  d_preprocessingPassRegistry.registerPass("bv-intro-pow2",
                                           std::move(bvIntroPow2));
  d_preprocessingPassRegistry.registerPass("bv-to-bool", std::move(bvToBool));
  d_preprocessingPassRegistry.registerPass("ext-rew-pre", std::move(extRewPre));
  d_preprocessingPassRegistry.registerPass("global-negate",
                                           std::move(globalNegate));
  d_preprocessingPassRegistry.registerPass("int-to-bv", std::move(intToBV));
  d_preprocessingPassRegistry.registerPass("ite-removal",
                                           std::move(iteRemoval));
  d_preprocessingPassRegistry.registerPass("ite-simp", std::move(iteSimp));
  d_preprocessingPassRegistry.registerPass("nl-ext-purify",
                                           std::move(nlExtPurify));
  d_preprocessingPassRegistry.registerPass("non-clausal-simp",
                                           std::move(nonClausalSimp));
  d_preprocessingPassRegistry.registerPass("miplib-trick",
                                           std::move(mipLibTrick));
  d_preprocessingPassRegistry.registerPass("quantifiers-preprocess",
                                           std::move(quantifiersPreprocess));
  d_preprocessingPassRegistry.registerPass("pseudo-boolean-processor",
                                           std::move(pbProc));
  d_preprocessingPassRegistry.registerPass("real-to-int", std::move(realToInt));
  d_preprocessingPassRegistry.registerPass("rewrite", std::move(rewrite));
  d_preprocessingPassRegistry.registerPass("sep-skolem-emp",
                                           std::move(sepSkolemEmp));
  d_preprocessingPassRegistry.registerPass("sort-inference",
                                           std::move(sortInfer));
  d_preprocessingPassRegistry.registerPass("static-learning",
                                           std::move(staticLearning));
  d_preprocessingPassRegistry.registerPass("sygus-infer",
                                           std::move(sygusInfer));
  d_preprocessingPassRegistry.registerPass("sym-break", std::move(sbProc));
  d_preprocessingPassRegistry.registerPass("synth-rr", std::move(srrProc));
  d_preprocessingPassRegistry.registerPass("theory-preprocess",
                                           std::move(theoryPreprocess));
  d_preprocessingPassRegistry.registerPass("quantifier-macros",
                                           std::move(quantifierMacros));
  d_preprocessingPassRegistry.registerPass("unconstrained-simplifier",
                                           std::move(unconstrainedSimplifier));
}

Node SmtEnginePrivate::expandDefinitions(TNode n, unordered_map<Node, Node, NodeHashFunction>& cache, bool expandOnly)
{
  stack<std::tuple<Node, Node, bool>> worklist;
  stack<Node> result;
  worklist.push(std::make_tuple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the output / rewritten node
  // and finally a flag tracking whether the children have been explored (i.e. if this is a downward
  // or upward pass).

  do {
    spendResource(options::preprocessStep());

    // n is the input / original
    // node is the output / result
    Node node;
    bool childrenPushed;
    std::tie(n, node, childrenPushed) = worklist.top();
    worklist.pop();

    // Working downwards
    if(!childrenPushed) {
      Kind k = n.getKind();

      // we can short circuit (variable) leaves
      if(n.isVar()) {
        SmtEngine::DefinedFunctionMap::const_iterator i = d_smt.d_definedFunctions->find(n);
        if(i != d_smt.d_definedFunctions->end()) {
          // replacement must be closed
          if((*i).second.getFormals().size() > 0) {
            result.push(d_smt.d_nodeManager->mkNode(kind::LAMBDA, d_smt.d_nodeManager->mkNode(kind::BOUND_VAR_LIST, (*i).second.getFormals()), (*i).second.getFormula()));
            continue;
          }
          // don't bother putting in the cache
          result.push((*i).second.getFormula());
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit = cache.find(n);
      if(cacheHit != cache.end()) {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it
      bool doExpand = false;
      if (k == kind::APPLY)
      {
        doExpand = true;
      }
      else if (k == kind::APPLY_UF)
      {
        // Always do beta-reduction here. The reason is that there may be
        // operators such as INTS_MODULUS in the body of the lambda that would
        // otherwise be introduced by beta-reduction via the rewriter, but are
        // not expanded here since the traversal in this function does not
        // traverse the operators of nodes. Hence, we beta-reduce here to
        // ensure terms in the body of the lambda are expanded during this
        // call.
        if (n.getOperator().getKind() == kind::LAMBDA)
        {
          doExpand = true;
        }
        else if (options::macrosQuant() || options::sygusInference())
        {
          // The above options assign substitutions to APPLY_UF, thus we check
          // here and expand if this operator corresponds to a defined function.
          doExpand = d_smt.isDefinedFunction(n.getOperator().toExpr());
        }
      }
      if (doExpand) {
        vector<Node> formals;
        TNode fm;
        if( n.getOperator().getKind() == kind::LAMBDA ){
          TNode op = n.getOperator();
          // lambda
          for( unsigned i=0; i<op[0].getNumChildren(); i++ ){
            formals.push_back( op[0][i] );
          }
          fm = op[1];
        }else{
          // application of a user-defined symbol
          TNode func = n.getOperator();
          SmtEngine::DefinedFunctionMap::const_iterator i = d_smt.d_definedFunctions->find(func);
          if(i == d_smt.d_definedFunctions->end()) {
            throw TypeCheckingException(n.toExpr(), string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (*i).second;
          formals = def.getFormals();

          if(Debug.isOn("expand")) {
            Debug("expand") << "found: " << n << endl;
            Debug("expand") << " func: " << func << endl;
            string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << endl;
          }
          if(Debug.isOn("expand")) {
            Debug("expand") << " defn: " << def.getFunction() << endl
                            << "       [";
            if(formals.size() > 0) {
              copy( formals.begin(), formals.end() - 1,
                    ostream_iterator<Node>(Debug("expand"), ", ") );
              Debug("expand") << formals.back();
            }
            Debug("expand") << "]" << endl
                            << "       " << def.getFunction().getType() << endl
                            << "       " << def.getFormula() << endl;
          }

          fm = def.getFormula();
        }

        Node instance = fm.substitute(formals.begin(),
                                      formals.end(),
                                      n.begin(),
                                      n.begin() + formals.size());
        Debug("expand") << "made : " << instance << endl;

        Node expanded = expandDefinitions(instance, cache, expandOnly);
        cache[n] = (n == expanded ? Node::null() : expanded);
        result.push(expanded);
        continue;

      } else if(! expandOnly) {
        // do not do any theory stuff if expandOnly is true

        theory::Theory* t = d_smt.d_theoryEngine->theoryOf(node);

        Assert(t != NULL);
        LogicRequest req(d_smt);
        node = t->expandDefinition(req, n);
      }

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(std::make_tuple(
          Node(n), node, true));  // Original and rewritten result

      for(size_t i = 0; i < node.getNumChildren(); ++i) {
        worklist.push(
            std::make_tuple(node[i],
                            node[i],
                            false));  // Rewrite the children of the result only
      }

    } else {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << endl;
      if(node.getNumChildren()>0) {
        //cout << "cons : " << node << endl;
        NodeBuilder<> nb(node.getKind());
        if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
          Debug("expand") << "op   : " << node.getOperator() << endl;
          //cout << "op   : " << node.getOperator() << endl;
          nb << node.getOperator();
        }
        for(size_t i = 0; i < node.getNumChildren(); ++i) {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          //cout << "exchld : " << expanded << endl;
          Debug("expand") << "exchld : " << expanded << endl;
          nb << expanded;
        }
        node = nb;
      }
      cache[n] = n == node ? Node::null() : node;           // Only cache once all subterms are expanded
      result.push(node);
    }
  } while(!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

// do dumping (before/after any preprocessing pass)
static void dumpAssertions(const char* key,
                           const AssertionPipeline& assertionList) {
  if( Dump.isOn("assertions") &&
      Dump.isOn(string("assertions:") + key) ) {
    // Push the simplified assertions to the dump output stream
    for(unsigned i = 0; i < assertionList.size(); ++ i) {
      TNode n = assertionList[i];
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
    }
  }
}

// returns false if simplification led to "false"
bool SmtEnginePrivate::simplifyAssertions()
{
  spendResource(options::preprocessStep());
  Assert(d_smt.d_pendingPops == 0);
  try {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    if (options::simplificationMode() != SIMPLIFICATION_MODE_NONE)
    {
      if (!options::unsatCores() && !options::fewerPreprocessingHoles())
      {
        // Perform non-clausal simplification
        PreprocessingPassResult res =
            d_preprocessingPassRegistry.getPass("non-clausal-simp")
                ->apply(&d_assertions);
        if (res == PreprocessingPassResult::CONFLICT)
        {
          return false;
        }
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if (  // check that option is on
          options::arithMLTrick() &&
          // miplib rewrites aren't safe in incremental mode
          !options::incrementalSolving() &&
          // only useful in arith
          d_smt.d_logic.isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          d_assertions.getRealAssertionsEnd() == d_assertions.size())
      {
        d_preprocessingPassRegistry.getPass("miplib-trick")
            ->apply(&d_assertions);
      } else {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass (either incrementalSolving is on, or miplib pbs are turned off)..." << endl;
      }
    }

    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // before ppRewrite check if only core theory for BV theory
    d_smt.d_theoryEngine->staticInitializeBVOptions(d_assertions.ref());

    // Theory preprocessing
    if (d_smt.d_earlyTheoryPP)
    {
      d_preprocessingPassRegistry.getPass("theory-preprocess")
          ->apply(&d_assertions);
    }

    // ITE simplification
    if (options::doITESimp()
        && (d_simplifyAssertionsDepth <= 1 || options::doITESimpOnRepeat()))
    {
      PreprocessingPassResult res =
          d_preprocessingPassRegistry.getPass("ite-simp")->apply(&d_assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        Chat() << "...ITE simplification found unsat..." << endl;
        return false;
      }
    }

    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // Unconstrained simplification
    if(options::unconstrainedSimp()) {
      d_preprocessingPassRegistry.getPass("unconstrained-simplifier")
          ->apply(&d_assertions);
    }

    if (options::repeatSimp()
        && options::simplificationMode() != SIMPLIFICATION_MODE_NONE
        && !options::unsatCores() && !options::fewerPreprocessingHoles())
    {
      PreprocessingPassResult res =
          d_preprocessingPassRegistry.getPass("non-clausal-simp")
              ->apply(&d_assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", d_assertions);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
  return true;
}

Result SmtEngine::check() {
  Assert(d_fullyInited);
  Assert(d_pendingPops == 0);

  Trace("smt") << "SmtEngine::check()" << endl;

  ResourceManager* resourceManager = d_private->getResourceManager();

  resourceManager->beginCall();

  // Only way we can be out of resource is if cumulative budget is on
  if (resourceManager->cumulativeLimitOn() &&
      resourceManager->out()) {
    Result::UnknownExplanation why = resourceManager->outOfResources() ?
                             Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::VALIDITY_UNKNOWN, why, d_filename);
  }

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  d_private->processAssertions();
  Trace("smt") << "SmtEngine::check(): done processing assertions" << endl;

  // Turn off stop only for QF_LRA
  // TODO: Bring up in a meeting where to put this
  if(options::decisionStopOnly() && !options::decisionMode.wasSetByUser() ){
    if( // QF_LRA
       (not d_logic.isQuantified() &&
        d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
        )){
      if (d_private->getIteSkolemMap().empty())
      {
        options::decisionStopOnly.set(false);
        d_decisionEngine->clearStrategies();
        Trace("smt") << "SmtEngine::check(): turning off stop only" << endl;
      }
    }
  }

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  resourceManager->endCall();
  Trace("limit") << "SmtEngine::check(): cumulative millis " << resourceManager->getTimeUsage()
                 << ", resources " << resourceManager->getResourceUsage() << endl;


  return Result(result, d_filename);
}

Result SmtEngine::quickCheck() {
  Assert(d_fullyInited);
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN, Result::REQUIRES_FULL_CHECK, d_filename);
}


void SmtEnginePrivate::collectSkolems(TNode n, set<TNode>& skolemSet, unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = getIteSkolemMap().find(n);
    if (it != getIteSkolemMap().end())
    {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    collectSkolems(n[k], skolemSet, cache);
  }
  cache[n] = true;
}

bool SmtEnginePrivate::checkForBadSkolems(TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = getIteSkolemMap().find(n);
    bool bad = false;
    if (it != getIteSkolemMap().end())
    {
      if (!((*it).first < n)) {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    if (checkForBadSkolems(n[k], skolem, cache)) {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

void SmtEnginePrivate::processAssertions() {
  TimerStat::CodeTimer paTimer(d_smt.d_stats->d_processAssertionsTime);
  spendResource(options::preprocessStep());
  Assert(d_smt.d_fullyInited);
  Assert(d_smt.d_pendingPops == 0);
  SubstitutionMap& top_level_substs =
      d_preprocessingPassContext->getTopLevelSubstitutions();

  // Dump the assertions
  dumpAssertions("pre-everything", d_assertions);

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() begin" << endl;
  Trace("smt") << "SmtEnginePrivate::processAssertions()" << endl;

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  if (d_assertions.size() == 0) {
    // nothing to do
    return;
  }

  if (options::bvGaussElim())
  {
    d_preprocessingPassRegistry.getPass("bv-gauss")->apply(&d_assertions);
  }

  if (d_assertionsProcessed && options::incrementalSolving()) {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    // Placeholder for storing substitutions
    d_preprocessingPassContext->setSubstitutionsIndex(d_assertions.size());
    d_assertions.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  d_assertions.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  // any assertions added beyond realAssertionsEnd must NOT affect the
  // equisatisfiability
  d_assertions.updateRealAssertionsEnd();

  // Assertions are NOT guaranteed to be rewritten by this point

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-definition-expansion" << endl;
  dumpAssertions("pre-definition-expansion", d_assertions);
  {
    Chat() << "expanding definitions..." << endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_definitionExpansionTime);
    unordered_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, expandDefinitions(d_assertions[i], cache));
    }
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-definition-expansion" << endl;
  dumpAssertions("post-definition-expansion", d_assertions);

  // save the assertions now
  THEORY_PROOF
    (
     for (unsigned i = 0; i < d_assertions.size(); ++i) {
       ProofManager::currentPM()->addAssertion(d_assertions[i].toExpr());
     }
     );

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  if (options::globalNegate())
  {
    // global negation of the formula
    d_preprocessingPassRegistry.getPass("global-negate")->apply(&d_assertions);
    d_smt.d_globalNegation = !d_smt.d_globalNegation;
  }

  if( options::nlExtPurify() ){
    d_preprocessingPassRegistry.getPass("nl-ext-purify")->apply(&d_assertions);
  }

  if( options::ceGuidedInst() ){
    //register sygus conjecture pre-rewrite (motivated by solution reconstruction)
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_smt.d_theoryEngine->getQuantifiersEngine()
          ->getSynthEngine()
          ->preregisterAssertion(d_assertions[i]);
    }
  }

  if (options::solveRealAsInt()) {
    d_preprocessingPassRegistry.getPass("real-to-int")->apply(&d_assertions);
  }

  if (options::solveIntAsBV() > 0)
  {
    d_preprocessingPassRegistry.getPass("int-to-bv")->apply(&d_assertions);
  }

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER &&
      !d_smt.d_logic.isPure(THEORY_BV) &&
      d_smt.d_logic.getLogicString() != "QF_UFBV" &&
      d_smt.d_logic.getLogicString() != "QF_ABV") {
    throw ModalException("Eager bit-blasting does not currently support theory combination. "
                         "Note that in a QF_BV problem UF symbols can be introduced for division. "
                         "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER
      && !options::incrementalSolving())
  {
    d_preprocessingPassRegistry.getPass("bv-ackermann")->apply(&d_assertions);
  }

  if (options::bvAbstraction() && !options::incrementalSolving())
  {
    d_preprocessingPassRegistry.getPass("bv-abstraction")->apply(&d_assertions);
  }

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  bool noConflict = true;

  if (options::extRewPrep())
  {
    d_preprocessingPassRegistry.getPass("ext-rew-pre")->apply(&d_assertions);
  }

  // Unconstrained simplification
  if(options::unconstrainedSimp()) {
    d_preprocessingPassRegistry.getPass("rewrite")->apply(&d_assertions);
    d_preprocessingPassRegistry.getPass("unconstrained-simplifier")
        ->apply(&d_assertions);
  }

  if(options::bvIntroducePow2())
  {
    d_preprocessingPassRegistry.getPass("bv-intro-pow2")->apply(&d_assertions);
  }

  if (options::unsatCores())
  {
    // special rewriting pass for unsat cores, since many of the passes below
    // are skipped
    d_preprocessingPassRegistry.getPass("rewrite")->apply(&d_assertions);
  }
  else
  {
    d_preprocessingPassRegistry.getPass("apply-substs")->apply(&d_assertions);
  }

  // Assertions ARE guaranteed to be rewritten by this point
#ifdef CVC4_ASSERTIONS
  for (unsigned i = 0; i < d_assertions.size(); ++i)
  {
    Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
  }
#endif

  // Lift bit-vectors of size 1 to bool
  if (options::bitvectorToBool())
  {
    d_preprocessingPassRegistry.getPass("bv-to-bool")->apply(&d_assertions);
  }
  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options::boolToBitvector())
  {
    d_preprocessingPassRegistry.getPass("bool-to-bv")->apply(&d_assertions);
  }
  if(options::sepPreSkolemEmp()) {
    d_preprocessingPassRegistry.getPass("sep-skolem-emp")->apply(&d_assertions);
  }

  if( d_smt.d_logic.isQuantified() ){
    //remove rewrite rules, apply pre-skolemization to existential quantifiers
    d_preprocessingPassRegistry.getPass("quantifiers-preprocess")
        ->apply(&d_assertions);
    if( options::macrosQuant() ){
      //quantifiers macro expansion
      d_preprocessingPassRegistry.getPass("quantifier-macros")
          ->apply(&d_assertions);
    }

    //fmf-fun : assume admissible functions, applying preprocessing reduction to FMF
    if( options::fmfFunWellDefined() ){
      quantifiers::FunDefFmf fdf;
      Assert( d_smt.d_fmfRecFunctionsDefined!=NULL );
      //must carry over current definitions (for incremental)
      for( context::CDList<Node>::const_iterator fit = d_smt.d_fmfRecFunctionsDefined->begin();
           fit != d_smt.d_fmfRecFunctionsDefined->end(); ++fit ) {
        Node f = (*fit);
        Assert( d_smt.d_fmfRecFunctionsAbs.find( f )!=d_smt.d_fmfRecFunctionsAbs.end() );
        TypeNode ft = d_smt.d_fmfRecFunctionsAbs[f];
        fdf.d_sorts[f] = ft;
        std::map< Node, std::vector< Node > >::iterator fcit = d_smt.d_fmfRecFunctionsConcrete.find( f );
        Assert( fcit!=d_smt.d_fmfRecFunctionsConcrete.end() );
        for( unsigned j=0; j<fcit->second.size(); j++ ){
          fdf.d_input_arg_inj[f].push_back( fcit->second[j] );
        }
      }
      fdf.simplify( d_assertions.ref() );
      //must store new definitions (for incremental)
      for( unsigned i=0; i<fdf.d_funcs.size(); i++ ){
        Node f = fdf.d_funcs[i];
        d_smt.d_fmfRecFunctionsAbs[f] = fdf.d_sorts[f];
        d_smt.d_fmfRecFunctionsConcrete[f].clear();
        for( unsigned j=0; j<fdf.d_input_arg_inj[f].size(); j++ ){
          d_smt.d_fmfRecFunctionsConcrete[f].push_back( fdf.d_input_arg_inj[f][j] );
        }
        d_smt.d_fmfRecFunctionsDefined->push_back( f );
      }
    }
    if (options::sygusInference())
    {
      d_preprocessingPassRegistry.getPass("sygus-infer")->apply(&d_assertions);
    }
  }

  if( options::sortInference() || options::ufssFairnessMonotone() ){
    d_preprocessingPassRegistry.getPass("sort-inference")->apply(&d_assertions);
  }

  if( options::pbRewrites() ){
    d_preprocessingPassRegistry.getPass("pseudo-boolean-processor")
        ->apply(&d_assertions);
  }

  if (options::synthRrPrep())
  {
    // do candidate rewrite rule synthesis
    d_preprocessingPassRegistry.getPass("synth-rr")->apply(&d_assertions);
  }

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-simplify" << endl;
  dumpAssertions("pre-simplify", d_assertions);
  Chat() << "simplifying assertions..." << endl;
  noConflict = simplifyAssertions();
  if(!noConflict){
    ++(d_smt.d_stats->d_simplifiedToFalse);
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-simplify" << endl;
  dumpAssertions("post-simplify", d_assertions);

  if (options::symmetryBreakerExp() && !options::incrementalSolving())
  {
    // apply symmetry breaking if not in incremental mode
    d_preprocessingPassRegistry.getPass("sym-break")->apply(&d_assertions);
  }

  if(options::doStaticLearning()) {
    d_preprocessingPassRegistry.getPass("static-learning")
        ->apply(&d_assertions);
  }
  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  {
    d_smt.d_stats->d_numAssertionsPre += d_assertions.size();
    d_preprocessingPassRegistry.getPass("ite-removal")->apply(&d_assertions);
    // This is needed because when solving incrementally, removeITEs may introduce
    // skolems that were solved for earlier and thus appear in the substitution
    // map.
    d_preprocessingPassRegistry.getPass("apply-substs")->apply(&d_assertions);
    d_smt.d_stats->d_numAssertionsPost += d_assertions.size();
  }

  dumpAssertions("pre-repeat-simplify", d_assertions);
  if(options::repeatSimp()) {
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-repeat-simplify" << endl;
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions();
    if (noConflict) {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the order in which these variables were introduced
      // during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr mapped to by sk.

      // cache for expression traversal
      unordered_map<Node, bool, NodeHashFunction> cache;

      // First, find all skolems that appear in the substitution map - their associated iteExpr will need
      // to be moved to the main assertion set
      set<TNode> skolemSet;
      SubstitutionMap::iterator pos = top_level_substs.begin();
      for (; pos != top_level_substs.end(); ++pos)
      {
        collectSkolems((*pos).first, skolemSet, cache);
        collectSkolems((*pos).second, skolemSet, cache);
      }

      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper assertion
      IteSkolemMap::iterator it = getIteSkolemMap().begin();
      IteSkolemMap::iterator iend = getIteSkolemMap().end();
      NodeBuilder<> builder(kind::AND);
      builder << d_assertions[d_assertions.getRealAssertionsEnd() - 1];
      vector<TNode> toErase;
      for (; it != iend; ++it) {
        if (skolemSet.find((*it).first) == skolemSet.end()) {
          TNode iteExpr = d_assertions[(*it).second];
          if (iteExpr.getKind() == kind::ITE &&
              iteExpr[1].getKind() == kind::EQUAL &&
              iteExpr[1][0] == (*it).first &&
              iteExpr[2].getKind() == kind::EQUAL &&
              iteExpr[2][0] == (*it).first) {
            cache.clear();
            bool bad = checkForBadSkolems(iteExpr[0], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[1][1], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[2][1], (*it).first, cache);
            if (!bad) {
              continue;
            }
          }
        }
        // Move this iteExpr into the main assertions
        builder << d_assertions[(*it).second];
        d_assertions[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
        toErase.push_back((*it).first);
      }
      if(builder.getNumChildren() > 1) {
        while (!toErase.empty()) {
          getIteSkolemMap().erase(toErase.back());
          toErase.pop_back();
        }
        d_assertions[d_assertions.getRealAssertionsEnd() - 1] =
            Rewriter::rewrite(Node(builder));
      }
      // TODO(b/1256): For some reason this is needed for some benchmarks, such as
      // QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      d_preprocessingPassRegistry.getPass("ite-removal")->apply(&d_assertions);
      d_preprocessingPassRegistry.getPass("apply-substs")->apply(&d_assertions);
      //      Assert(iteRewriteAssertionsEnd == d_assertions.size());
    }
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-repeat-simplify" << endl;
  }
  dumpAssertions("post-repeat-simplify", d_assertions);

  if (options::rewriteApplyToConst())
  {
    d_preprocessingPassRegistry.getPass("apply-to-const")->apply(&d_assertions);
  }

  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones
#ifdef CVC4_ASSERTIONS
  unsigned iteRewriteAssertionsEnd = d_assertions.size();
#endif

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  Debug("smt") << "SmtEnginePrivate::processAssertions() POST SIMPLIFICATION" << endl;
  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  d_preprocessingPassRegistry.getPass("theory-preprocess")
      ->apply(&d_assertions);

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER)
  {
    d_preprocessingPassRegistry.getPass("bv-eager-atoms")->apply(&d_assertions);
  }

  //notify theory engine new preprocessed assertions
  d_smt.d_theoryEngine->notifyPreprocessedAssertions( d_assertions.ref() );

  // Push the formula to decision engine
  if(noConflict) {
    Chat() << "pushing to decision engine..." << endl;
    Assert(iteRewriteAssertionsEnd == d_assertions.size());
    d_smt.d_decisionEngine->addAssertions(d_assertions);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() end" << endl;
  dumpAssertions("post-everything", d_assertions);

  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_preprocessingPassContext->recordSymbolsInAssertions(d_assertions.ref());
  }

  // Push the formula to SAT
  {
    Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_cnfConversionTime);
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      Chat() << "+ " << d_assertions[i] << std::endl;
      d_smt.d_propEngine->assertFormula(d_assertions[i]);
    }
  }

  d_assertionsProcessed = true;

  d_assertions.clear();
  getIteSkolemMap().clear();
}

void SmtEnginePrivate::addFormula(TNode n, bool inUnsatCore, bool inInput)
{
  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << "), inUnsatCore = " << inUnsatCore << ", inInput = " << inInput << endl;

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {

        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
    // rewrite rules are by default in the unsat core because
    // they need to be applied until saturation
    if(options::unsatCores() &&
       n.getKind() == kind::REWRITE_RULE ){
      ProofManager::currentPM()->addUnsatCore(n.toExpr());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n);
  //d_assertions.push_back(Rewriter::rewrite(n));
}

void SmtEngine::ensureBoolean(const Expr& e)
{
  Type type = e.getType(options::typeChecking());
  Type boolType = d_exprManager->booleanType();
  if(type != boolType) {
    stringstream ss;
    ss << "Expected " << boolType << "\n"
       << "The assertion : " << e << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(e, ss.str());
  }
}

Result SmtEngine::checkSat(const Expr& assumption, bool inUnsatCore)
{
  return checkSatisfiability(assumption, inUnsatCore, false);
}

Result SmtEngine::checkSat(const vector<Expr>& assumptions, bool inUnsatCore)
{
  return checkSatisfiability(assumptions, inUnsatCore, false);
}

Result SmtEngine::query(const Expr& assumption, bool inUnsatCore)
{
  Assert(!assumption.isNull());
  return checkSatisfiability(assumption, inUnsatCore, true);
}

Result SmtEngine::query(const vector<Expr>& assumptions, bool inUnsatCore)
{
  return checkSatisfiability(assumptions, inUnsatCore, true);
}

Result SmtEngine::checkSatisfiability(const Expr& expr,
                                      bool inUnsatCore,
                                      bool isQuery)
{
  return checkSatisfiability(
      expr.isNull() ? vector<Expr>() : vector<Expr>{expr},
      inUnsatCore,
      isQuery);
}

Result SmtEngine::checkSatisfiability(const vector<Expr>& assumptions,
                                      bool inUnsatCore,
                                      bool isQuery)
{
  try
  {
    SmtScope smts(this);
    finalOptionsAreSet();
    doPendingPops();

    Trace("smt") << "SmtEngine::" << (isQuery ? "query" : "checkSat") << "("
                 << assumptions << ")" << endl;

    if(d_queryMade && !options::incrementalSolving()) {
      throw ModalException("Cannot make multiple queries unless "
                           "incremental solving is enabled "
                           "(try --incremental)");
    }

    // check to see if a postsolve() is pending
    if(d_needPostsolve) {
      d_theoryEngine->postsolve();
      d_needPostsolve = false;
    }
    // Note that a query has been made
    d_queryMade = true;
    // reset global negation
    d_globalNegation = false;

    bool didInternalPush = false;

    setProblemExtended(true);

    if (isQuery)
    {
      size_t size = assumptions.size();
      if (size > 1)
      {
        /* Assume: not (BIGAND assumptions)  */
        d_assumptions.push_back(
            d_exprManager->mkExpr(kind::AND, assumptions).notExpr());
      }
      else if (size == 1)
      {
        /* Assume: not expr  */
        d_assumptions.push_back(assumptions[0].notExpr());
      }
    }
    else
    {
      /* Assume: BIGAND assumptions  */
      d_assumptions = assumptions;
    }

    if (!d_assumptions.empty())
    {
      internalPush();
      didInternalPush = true;
    }

    Result r(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    for (Expr e : d_assumptions)
    {
      // Substitute out any abstract values in ex.
      e = d_private->substituteAbstractValues(Node::fromExpr(e)).toExpr();
      Assert(e.getExprManager() == d_exprManager);
      // Ensure expr is type-checked at this point.
      ensureBoolean(e);

      /* Add assumption  */
      if (d_assertionList != NULL)
      {
        d_assertionList->push_back(e);
      }
      d_private->addFormula(e.getNode(), inUnsatCore);
    }

    r = isQuery ? check().asValidityResult() : check().asSatisfiabilityResult();

    if ((options::solveRealAsInt() || options::solveIntAsBV() > 0)
        && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    }
    // flipped if we did a global negation
    if (d_globalNegation)
    {
      Trace("smt") << "SmtEngine::process global negate " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        r = Result(Result::SAT);
      }
      else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        // only if satisfaction complete
        if (d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV))
        {
          r = Result(Result::UNSAT);
        }
        else
        {
          r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
        }
      }
      Trace("smt") << "SmtEngine::global negate returned " << r << std::endl;
    }

    d_needPostsolve = true;

    // Dump the query if requested
    if (Dump.isOn("benchmark"))
    {
      size_t size = assumptions.size();
      // the expr already got dumped out if assertion-dumping is on
      if (isQuery && size == 1)
      {
        Dump("benchmark") << QueryCommand(assumptions[0]);
      }
      else if (size == 0)
      {
        Dump("benchmark") << CheckSatCommand();
      }
      else
      {
        Dump("benchmark") << CheckSatAssumingCommand(d_assumptions);
      }
    }

    d_propEngine->resetTrail();

    // Pop the context
    if (didInternalPush)
    {
      internalPop();
    }

    // Remember the status
    d_status = r;

    setProblemExtended(false);

    Trace("smt") << "SmtEngine::" << (isQuery ? "query" : "checkSat") << "("
                 << assumptions << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if(options::checkModels()) {
      // TODO (#1693) check model when unknown result?
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if(options::checkProofs()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        TimerStat::CodeTimer checkProofTimer(d_stats->d_checkProofTime);
        checkProof();
      }
    }
    // Check that UNSAT results generate an unsat core correctly.
    if(options::checkUnsatCores()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
        checkUnsatCore();
      }
    }
    // Check that synthesis solutions satisfy the conjecture
    if (options::checkSynthSol()
        && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      checkSynthSolution();
    }

    return r;
  } catch (UnsafeInterruptException& e) {
    AlwaysAssert(d_private->getResourceManager()->out());
    Result::UnknownExplanation why = d_private->getResourceManager()->outOfResources() ?
      Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::SAT_UNKNOWN, why, d_filename);
  }
}

vector<Expr> SmtEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  SmtScope smts(this);
  if (!options::unsatAssumptions())
  {
    throw ModalException(
        "Cannot get unsat assumptions when produce-unsat-assumptions option "
        "is off.");
  }
  if (d_status.isNull()
      || d_status.asSatisfiabilityResult() != Result::UNSAT
      || d_problemExtended)
  {
    throw RecoverableModalException(
        "Cannot get unsat assumptions unless immediately preceded by "
        "UNSAT/VALID response.");
  }
  finalOptionsAreSet();
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << GetUnsatAssumptionsCommand();
  }
  UnsatCore core = getUnsatCoreInternal();
  vector<Expr> res;
  for (const Expr& e : d_assumptions)
  {
    if (find(core.begin(), core.end(), e) != core.end()) { res.push_back(e); }
  }
  return res;
}

Result SmtEngine::checkSynth(const Expr& e)
{
  SmtScope smts(this);
  Trace("smt") << "Check synth: " << e << std::endl;
  Trace("smt-synth") << "Check synthesis conjecture: " << e << std::endl;
  return checkSatisfiability(e, true, false);
}

Result SmtEngine::assertFormula(const Expr& ex, bool inUnsatCore)
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();

  Trace("smt") << "SmtEngine::assertFormula(" << ex << ")" << endl;

  if (Dump.isOn("raw-benchmark")) {
    Dump("raw-benchmark") << AssertCommand(ex);
  }

  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  ensureBoolean(e);
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e);
  }
  d_private->addFormula(e.getNode(), inUnsatCore);
  return quickCheck().asValidityResult();
}/* SmtEngine::assertFormula() */

Node SmtEngine::postprocess(TNode node, TypeNode expectedType) const {
  return node;
}

Expr SmtEngine::simplify(const Expr& ex)
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT simplify(" << ex << ")" << endl;

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SimplifyCommand(ex);
  }

  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  if( options::typeChecking() ) {
    e.getType(true); // ensure expr is type-checked at this point
  }

  // Make sure all preprocessing is done
  d_private->processAssertions();
  Node n = d_private->simplify(Node::fromExpr(e));
  n = postprocess(n, TypeNode::fromType(e.getType()));
  return n.toExpr();
}

Expr SmtEngine::expandDefinitions(const Expr& ex)
{
  d_private->spendResource(options::preprocessStep());

  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT expandDefinitions(" << ex << ")" << endl;

  // Substitute out any abstract values in ex.
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  if(options::typeChecking()) {
    // Ensure expr is type-checked at this point.
    e.getType(true);
  }
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ExpandDefinitionsCommand(e);
  }
  unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_private->expandDefinitions(Node::fromExpr(e), cache, /* expandOnly = */ true);
  n = postprocess(n, TypeNode::fromType(e.getType()));

  return n.toExpr();
}

// TODO(#1108): Simplify the error reporting of this method.
Expr SmtEngine::getValue(const Expr& ex) const
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetValueCommand(ex);
  }

  if(!options::produceModels()) {
    const char* msg =
      "Cannot get value when produce-models options is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get value unless immediately preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }

  // Substitute out any abstract values in ex.
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  // Ensure expr is type-checked at this point.
  e.getType(options::typeChecking());

  // do not need to apply preprocessing substitutions (should be recorded
  // in model already)

  Node n = Node::fromExpr(e);
  Trace("smt") << "--- getting value of " << n << endl;
  TypeNode expectedType = n.getType();

  // Expand, then normalize
  unordered_map<Node, Node, NodeHashFunction> cache;
  n = d_private->expandDefinitions(n, cache);
  // There are two ways model values for terms are computed (for historical
  // reasons).  One way is that used in check-model; the other is that
  // used by the Model classes.  It's not clear to me exactly how these
  // two are different, but they need to be unified.  This ugly hack here
  // is to fix bug 554 until we can revamp boolean-terms and models [MGD]

  //AJR : necessary?
  if(!n.getType().isFunction()) {
    n = Rewriter::rewrite(n);
  }

  Trace("smt") << "--- getting value of " << n << endl;
  TheoryModel* m = d_theoryEngine->getModel();
  Node resultNode;
  if(m != NULL) {
    resultNode = m->getValue(n);
  }
  Trace("smt") << "--- got value " << n << " = " << resultNode << endl;
  resultNode = postprocess(resultNode, expectedType);
  Trace("smt") << "--- model-post returned " << resultNode << endl;
  Trace("smt") << "--- model-post returned " << resultNode.getType() << endl;
  Trace("smt") << "--- model-post expected " << expectedType << endl;

  // type-check the result we got
  Assert(resultNode.isNull() || resultNode.getType().isSubtypeOf(expectedType),
         "Run with -t smt for details.");

  // ensure it's a constant
  Assert(resultNode.getKind() == kind::LAMBDA || resultNode.isConst());

  if(options::abstractValues() && resultNode.getType().isArray()) {
    resultNode = d_private->mkAbstractValue(resultNode);
    Trace("smt") << "--- abstract value >> " << resultNode << endl;
  }

  return resultNode.toExpr();
}

bool SmtEngine::addToAssignment(const Expr& ex) {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  Type type = e.getType(options::typeChecking());
  // must be Boolean
  PrettyCheckArgument(
      type.isBoolean(), e,
      "expected Boolean-typed variable or function application "
      "in addToAssignment()" );
  Node n = e.getNode();
  // must be an APPLY of a zero-ary defined function, or a variable
  PrettyCheckArgument(
      ( ( n.getKind() == kind::APPLY &&
          ( d_definedFunctions->find(n.getOperator()) !=
            d_definedFunctions->end() ) &&
          n.getNumChildren() == 0 ) ||
        n.isVar() ), e,
      "expected variable or defined-function application "
      "in addToAssignment(),\ngot %s", e.toString().c_str() );
  if(!options::produceAssignments()) {
    return false;
  }
  if(d_assignments == NULL) {
    d_assignments = new(true) AssignmentSet(d_context);
  }
  d_assignments->insert(n);

  return true;
}

// TODO(#1108): Simplify the error reporting of this method.
vector<pair<Expr, Expr>> SmtEngine::getAssignment()
{
  Trace("smt") << "SMT getAssignment()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssignmentCommand();
  }
  if(!options::produceAssignments()) {
    const char* msg =
      "Cannot get the current assignment when "
      "produce-assignments option is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT  ||
     d_problemExtended) {
    const char* msg =
      "Cannot get the current assignment unless immediately "
      "preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }

  vector<pair<Expr,Expr>> res;
  if (d_assignments != nullptr)
  {
    TypeNode boolType = d_nodeManager->booleanType();
    TheoryModel* m = d_theoryEngine->getModel();
    for (AssignmentSet::key_iterator i = d_assignments->key_begin(),
                                     iend = d_assignments->key_end();
         i != iend;
         ++i)
    {
      Node as = *i;
      Assert(as.getType() == boolType);

      Trace("smt") << "--- getting value of " << as << endl;

      // Expand, then normalize
      unordered_map<Node, Node, NodeHashFunction> cache;
      Node n = d_private->expandDefinitions(as, cache);
      n = Rewriter::rewrite(n);

      Trace("smt") << "--- getting value of " << n << endl;
      Node resultNode;
      if (m != nullptr)
      {
        resultNode = m->getValue(n);
      }

      // type-check the result we got
      Assert(resultNode.isNull() || resultNode.getType() == boolType);

      // ensure it's a constant
      Assert(resultNode.isConst());

      Assert(as.getKind() == kind::APPLY || as.isVar());
      Assert(as.getKind() != kind::APPLY || as.getNumChildren() == 0);
      res.emplace_back(as.toExpr(), resultNode.toExpr());
    }
  }
  return res;
}

void SmtEngine::addToModelCommandAndDump(const Command& c, uint32_t flags, bool userVisible, const char* dumpTag) {
  Trace("smt") << "SMT addToModelCommandAndDump(" << c << ")" << endl;
  SmtScope smts(this);
  // If we aren't yet fully inited, the user might still turn on
  // produce-models.  So let's keep any commands around just in
  // case.  This is useful in two cases: (1) SMT-LIBv1 auto-declares
  // sort "U" in QF_UF before setLogic() is run and we still want to
  // support finding card(U) with --finite-model-find, and (2) to
  // decouple SmtEngine and ExprManager if the user does a few
  // ExprManager::mkSort() before SmtEngine::setOption("produce-models")
  // and expects to find their cardinalities in the model.
  if(/* userVisible && */
     (!d_fullyInited || options::produceModels()) &&
     (flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
    doPendingPops();
    if(flags & ExprManager::VAR_FLAG_GLOBAL) {
      d_modelGlobalCommands.push_back(c.clone());
    } else {
      d_modelCommands->push_back(c.clone());
    }
  }
  if(Dump.isOn(dumpTag)) {
    if(d_fullyInited) {
      Dump(dumpTag) << c;
    } else {
      d_dumpCommands.push_back(c.clone());
    }
  }
}

// TODO(#1108): Simplify the error reporting of this method.
Model* SmtEngine::getModel() {
  Trace("smt") << "SMT getModel()" << endl;
  SmtScope smts(this);

  finalOptionsAreSet();

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetModelCommand();
  }

  if (!options::assignFunctionValues())
  {
    const char* msg =
        "Cannot get the model when --assign-function-values is false.";
    throw RecoverableModalException(msg);
  }

  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get the current model unless immediately "
      "preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }
  if(!options::produceModels()) {
    const char* msg =
      "Cannot get model when produce-models options is off.";
    throw ModalException(msg);
  }
  TheoryModel* m = d_theoryEngine->getModel();

  if (options::produceModelCores())
  {
    // If we enabled model cores, we compute a model core for m based on our
    // assertions using the model core builder utility
    std::vector<Expr> easserts = getAssertions();
    ModelCoreBuilder::setModelCore(easserts, m);
  }
  m->d_inputName = d_filename;
  return m;
}

std::pair<Expr, Expr> SmtEngine::getSepHeapAndNilExpr(void)
{
  if (!d_logic.isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot obtain separation logic expressions if not using the "
        "separation logic theory.";
    throw RecoverableModalException(msg);
  }
  NodeManagerScope nms(d_nodeManager);
  Expr heap;
  Expr nil;
  Model* m = getModel();
  if (m->getHeapModel(heap, nil))
  {
    return std::make_pair(heap, nil);
  }
  InternalError(
      "SmtEngine::getSepHeapAndNilExpr(): failed to obtain heap/nil "
      "expressions from theory model.");
}

Expr SmtEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Expr SmtEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

UnsatCore SmtEngine::getUnsatCoreInternal()
{
#if IS_PROOFS_BUILD
  if (!options::unsatCores())
  {
    throw ModalException(
        "Cannot get an unsat core when produce-unsat-cores option is off.");
  }
  if (d_status.isNull() || d_status.asSatisfiabilityResult() != Result::UNSAT
      || d_problemExtended)
  {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by UNSAT/VALID "
        "response.");
  }

  d_proofManager->traceUnsatCore();  // just to trigger core creation
  return UnsatCore(this, d_proofManager->extractUnsatCore());
#else  /* IS_PROOFS_BUILD */
  throw ModalException(
      "This build of CVC4 doesn't have proof support (required for unsat "
      "cores).");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::checkUnsatCore() {
  Assert(options::unsatCores(), "cannot check unsat core if unsat cores are turned off");

  Notice() << "SmtEngine::checkUnsatCore(): generating unsat core" << endl;
  UnsatCore core = getUnsatCore();

  SmtEngine coreChecker(d_exprManager);
  coreChecker.setLogic(getLogicInfo());

  PROOF(
  std::vector<Command*>::const_iterator itg = d_defineCommands.begin();
  for (; itg != d_defineCommands.end();  ++itg) {
    (*itg)->invoke(&coreChecker);
  }
  );

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions (size == " << core.size() << ")" << endl;
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Notice() << "SmtEngine::checkUnsatCore(): pushing core member " << *i << endl;
    coreChecker.assertFormula(*i);
  }
  const bool checkUnsatCores = options::checkUnsatCores();
  Result r;
  try {
    options::checkUnsatCores.set(false);
    options::checkProofs.set(false);
    r = coreChecker.checkSat();
  } catch(...) {
    options::checkUnsatCores.set(checkUnsatCores);
    throw;
  }
  Notice() << "SmtEngine::checkUnsatCore(): result is " << r << endl;
  if(r.asSatisfiabilityResult().isUnknown()) {
    InternalError("SmtEngine::checkUnsatCore(): could not check core result unknown.");
  }

  if(r.asSatisfiabilityResult().isSat()) {
    InternalError("SmtEngine::checkUnsatCore(): produced core was satisfiable.");
  }
}

void SmtEngine::checkModel(bool hardFailure) {
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(d_assertionList != NULL, "don't have an assertion list to check in SmtEngine::checkModel()");

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  Notice() << "SmtEngine::checkModel(): generating model" << endl;
  TheoryModel* m = d_theoryEngine->getModel();

  // check-model is not guaranteed to succeed if approximate values were used
  if (m->hasApproximations())
  {
    Warning()
        << "WARNING: running check-model on a model with approximate values..."
        << endl;
  }

  // Check individual theory assertions
  d_theoryEngine->checkTheoryAssertionsWithModel(hardFailure);

  // Output the model
  Notice() << *m;

  // We have a "fake context" for the substitution map (we don't need it
  // to be context-dependent)
  context::Context fakeContext;
  SubstitutionMap substitutions(&fakeContext, /* substituteUnderQuantifiers = */ false);

  for(size_t k = 0; k < m->getNumCommands(); ++k) {
    const DeclareFunctionCommand* c = dynamic_cast<const DeclareFunctionCommand*>(m->getCommand(k));
    Notice() << "SmtEngine::checkModel(): model command " << k << " : " << m->getCommand(k) << endl;
    if(c == NULL) {
      // we don't care about DECLARE-DATATYPES, DECLARE-SORT, ...
      Notice() << "SmtEngine::checkModel(): skipping..." << endl;
    } else {
      // We have a DECLARE-FUN:
      //
      // We'll first do some checks, then add to our substitution map
      // the mapping: function symbol |-> value

      Expr func = c->getFunction();
      Node val = m->getValue(func);

      Notice() << "SmtEngine::checkModel(): adding substitution: " << func << " |-> " << val << endl;

      // (1) if the value is a lambda, ensure the lambda doesn't contain the
      // function symbol (since then the definition is recursive)
      if (val.getKind() == kind::LAMBDA) {
        // first apply the model substitutions we have so far
        Debug("boolean-terms") << "applying subses to " << val[1] << endl;
        Node n = substitutions.apply(val[1]);
        Debug("boolean-terms") << "++ got " << n << endl;
        // now check if n contains func by doing a substitution
        // [func->func2] and checking equality of the Nodes.
        // (this just a way to check if func is in n.)
        SubstitutionMap subs(&fakeContext);
        Node func2 = NodeManager::currentNM()->mkSkolem("", TypeNode::fromType(func.getType()), "", NodeManager::SKOLEM_NO_NOTIFY);
        subs.addSubstitution(func, func2);
        if(subs.apply(n) != n) {
          Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE DEFINED IN TERMS OF ITSELF ***" << endl;
          stringstream ss;
          ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
             << "considering model value for " << func << endl
             << "body of lambda is:   " << val << endl;
          if(n != val[1]) {
            ss << "body substitutes to: " << n << endl;
          }
          ss << "so " << func << " is defined in terms of itself." << endl
             << "Run with `--check-models -v' for additional diagnostics.";
          InternalError(ss.str());
        }
      }

      // (2) check that the value is actually a value
      else if (!val.isConst()) {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT A CONSTANT ***" << endl;
        stringstream ss;
        ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
           << "model value for " << func << endl
           << "             is " << val << endl
           << "and that is not a constant (.isConst() == false)." << endl
           << "Run with `--check-models -v' for additional diagnostics.";
        InternalError(ss.str());
      }

      // (3) check that it's the correct (sub)type
      // This was intended to be a more general check, but for now we can't do that because
      // e.g. "1" is an INT, which isn't a subrange type [1..10] (etc.).
      else if(func.getType().isInteger() && !val.getType().isInteger()) {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT CORRECT TYPE ***" << endl;
        stringstream ss;
        ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
           << "model value for " << func << endl
           << "             is " << val << endl
           << "value type is     " << val.getType() << endl
           << "should be of type " << func.getType() << endl
           << "Run with `--check-models -v' for additional diagnostics.";
        InternalError(ss.str());
      }

      // (4) checks complete, add the substitution
      Debug("boolean-terms") << "cm: adding subs " << func << " :=> " << val << endl;
      substitutions.addSubstitution(func, val);
    }
  }

  // Now go through all our user assertions checking if they're satisfied.
  for(AssertionList::const_iterator i = d_assertionList->begin(); i != d_assertionList->end(); ++i) {
    Notice() << "SmtEngine::checkModel(): checking assertion " << *i << endl;
    Node n = Node::fromExpr(*i);

    // Apply any define-funs from the problem.
    {
      unordered_map<Node, Node, NodeHashFunction> cache;
      n = d_private->expandDefinitions(n, cache);
    }
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << endl;

    // Apply our model value substitutions.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << endl;

    if( n.getKind() != kind::REWRITE_RULE ){
      // In case it's a quantifier (or contains one), look up its value before
      // simplifying, or the quantifier might be irreparably altered.
      n = m->getValue(n);
      Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;
    } else {
      // Note this "skip" is done here, rather than above.  This is
      // because (1) the quantifier could in principle simplify to false,
      // which should be reported, and (2) checking for the quantifier
      // above, before simplification, doesn't catch buried quantifiers
      // anyway (those not at the top-level).
      Notice() << "SmtEngine::checkModel(): -- skipping rewrite-rules assertion"
               << endl;
      continue;
    }

    // Simplify the result.
    n = d_private->simplify(n);
    Notice() << "SmtEngine::checkModel(): -- simplifies to  " << n << endl;

    // Replace the already-known ITEs (this is important for ground ITEs under quantifiers).
    n = d_private->d_iteRemover.replace(n);
    Notice() << "SmtEngine::checkModel(): -- ite replacement gives " << n << endl;

    // Apply our model value substitutions (again), as things may have been simplified.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- re-substitutes to " << n << endl;

    // As a last-ditch effort, ask model to simplify it.
    // Presently, this is only an issue for quantifiers, which can have a value
    // but don't show up in our substitution map above.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- model-substitutes to " << n << endl;

    if( d_logic.isQuantified() ){
      // AJR: since quantified formulas are not checkable, we assign them to true/false based on the satisfying assignment.
      // however, quantified formulas can be modified during preprocess, so they may not correspond to those in the satisfying assignment.
      // hence we use a relaxed version of check model here.
      // this is necessary until preprocessing passes explicitly record how they rewrite quantified formulas
      if( hardFailure && !n.isConst() && n.getKind() != kind::LAMBDA ){
        Notice() << "SmtEngine::checkModel(): -- relax check model wrt quantified formulas..." << endl;
        AlwaysAssert( quantifiers::QuantifiersRewriter::containsQuantifiers( n ) );
        Warning() << "Warning : SmtEngine::checkModel(): cannot check simplified assertion : " << n << endl;
        continue;
      }
    }else{
      AlwaysAssert(!hardFailure || n.isConst() || n.getKind() == kind::LAMBDA);
    }
    // The result should be == true.
    if(n != NodeManager::currentNM()->mkConst(true)) {
      Notice() << "SmtEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
               << endl;
      stringstream ss;
      ss << "SmtEngine::checkModel(): "
         << "ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
         << "assertion:     " << *i << endl
         << "simplifies to: " << n << endl
         << "expected `true'." << endl
         << "Run with `--check-models -v' for additional diagnostics.";
      if(hardFailure) {
        InternalError(ss.str());
      } else {
        Warning() << ss.str() << endl;
      }
    }
  }
  Notice() << "SmtEngine::checkModel(): all assertions checked out OK !" << endl;
}

void SmtEngine::checkSynthSolution()
{
  NodeManager* nm = NodeManager::currentNM();
  Notice() << "SmtEngine::checkSynthSolution(): checking synthesis solution" << endl;
  map<Node, Node> sol_map;
  /* Get solutions and build auxiliary vectors for substituting */
  d_theoryEngine->getSynthSolutions(sol_map);
  if (sol_map.empty())
  {
    Trace("check-synth-sol") << "No solution to check!\n";
    return;
  }
  Trace("check-synth-sol") << "Got solution map:\n";
  std::vector<Node> function_vars, function_sols;
  for (const auto& pair : sol_map)
  {
    Trace("check-synth-sol") << pair.first << " --> " << pair.second << "\n";
    function_vars.push_back(pair.first);
    function_sols.push_back(pair.second);
  }
  Trace("check-synth-sol") << "Starting new SMT Engine\n";
  /* Start new SMT engine to check solutions */
  SmtEngine solChecker(d_exprManager);
  solChecker.setLogic(getLogicInfo());
  setOption("check-synth-sol", SExpr("false"));

  Trace("check-synth-sol") << "Retrieving assertions\n";
  // Build conjecture from original assertions
  if (d_assertionList == NULL)
  {
    Trace("check-synth-sol") << "No assertions to check\n";
    return;
  }
  for (AssertionList::const_iterator i = d_assertionList->begin();
       i != d_assertionList->end();
       ++i)
  {
    Notice() << "SmtEngine::checkSynthSolution(): checking assertion " << *i << endl;
    Trace("check-synth-sol") << "Retrieving assertion " << *i << "\n";
    Node conj = Node::fromExpr(*i);
    // Apply any define-funs from the problem.
    {
      unordered_map<Node, Node, NodeHashFunction> cache;
      conj = d_private->expandDefinitions(conj, cache);
    }
    Notice() << "SmtEngine::checkSynthSolution(): -- expands to " << conj << endl;
    Trace("check-synth-sol") << "Expanded assertion " << conj << "\n";
    if (conj.getKind() != kind::FORALL)
    {
      Trace("check-synth-sol") << "Not a checkable assertion.\n";
      continue;
    }

    // Apply solution map to conjecture body
    Node conjBody;
    /* Whether property is quantifier free */
    if (conj[1].getKind() != kind::EXISTS)
    {
      conjBody = conj[1].substitute(function_vars.begin(),
                                    function_vars.end(),
                                    function_sols.begin(),
                                    function_sols.end());
    }
    else
    {
      conjBody = conj[1][1].substitute(function_vars.begin(),
                                       function_vars.end(),
                                       function_sols.begin(),
                                       function_sols.end());

      /* Skolemize property */
      std::vector<Node> vars, skos;
      for (unsigned j = 0, size = conj[1][0].getNumChildren(); j < size; ++j)
      {
        vars.push_back(conj[1][0][j]);
        std::stringstream ss;
        ss << "sk_" << j;
        skos.push_back(nm->mkSkolem(ss.str(), conj[1][0][j].getType()));
        Trace("check-synth-sol") << "\tSkolemizing " << conj[1][0][j] << " to "
                                 << skos.back() << "\n";
      }
      conjBody = conjBody.substitute(
          vars.begin(), vars.end(), skos.begin(), skos.end());
    }
    Notice() << "SmtEngine::checkSynthSolution(): -- body substitutes to "
             << conjBody << endl;
    Trace("check-synth-sol") << "Substituted body of assertion to " << conjBody
                             << "\n";
    solChecker.assertFormula(conjBody.toExpr());
    Result r = solChecker.checkSat();
    Notice() << "SmtEngine::checkSynthSolution(): result is " << r << endl;
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.asSatisfiabilityResult().isUnknown())
    {
      InternalError(
          "SmtEngine::checkSynthSolution(): could not check solution, result "
          "unknown.");
    }
    else if (r.asSatisfiabilityResult().isSat())
    {
      InternalError(
          "SmtEngine::checkSynthSolution(): produced solution leads to "
          "satisfiable negated conjecture.");
    }
    solChecker.resetAssertions();
  }
}

// TODO(#1108): Simplify the error reporting of this method.
UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetUnsatCoreCommand();
  }
  return getUnsatCoreInternal();
}

// TODO(#1108): Simplify the error reporting of this method.
const Proof& SmtEngine::getProof()
{
  Trace("smt") << "SMT getProof()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetProofCommand();
  }
#if IS_PROOFS_BUILD
  if(!options::proof()) {
    throw ModalException("Cannot get a proof when produce-proofs option is off.");
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::UNSAT ||
     d_problemExtended) {
    throw RecoverableModalException(
        "Cannot get a proof unless immediately preceded by UNSAT/VALID "
        "response.");
  }

  return ProofManager::getProof(this);
#else /* IS_PROOFS_BUILD */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::printInstantiations( std::ostream& out ) {
  SmtScope smts(this);
  if( options::instFormatMode()==INST_FORMAT_MODE_SZS ){
    out << "% SZS output start Proof for " << d_filename.c_str() << std::endl;
  }
  if( d_theoryEngine ){
    d_theoryEngine->printInstantiations( out );
  }else{
    Assert( false );
  }
  if( options::instFormatMode()==INST_FORMAT_MODE_SZS ){
    out << "% SZS output end Proof for " << d_filename.c_str() << std::endl;
  }
}

void SmtEngine::printSynthSolution( std::ostream& out ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    d_theoryEngine->printSynthSolution( out );
  }else{
    Assert( false );
  }
}

void SmtEngine::getSynthSolutions(std::map<Expr, Expr>& sol_map)
{
  SmtScope smts(this);
  map<Node, Node> sol_mapn;
  Assert(d_theoryEngine != nullptr);
  d_theoryEngine->getSynthSolutions(sol_mapn);
  for (std::pair<const Node, Node>& s : sol_mapn)
  {
    sol_map[s.first.toExpr()] = s.second.toExpr();
  }
}

Expr SmtEngine::doQuantifierElimination(const Expr& e, bool doFull, bool strict)
{
  SmtScope smts(this);
  if(!d_logic.isPure(THEORY_ARITH) && strict){
    Warning() << "Unexpected logic for quantifier elimination " << d_logic << endl;
  }
  Trace("smt-qe") << "Do quantifier elimination " << e << std::endl;
  Node n_e = Node::fromExpr( e );
  if (n_e.getKind() != kind::EXISTS && n_e.getKind() != kind::FORALL)
  {
    throw ModalException(
        "Expecting a quantified formula as argument to get-qe.");
  }
  //tag the quantified formula with the quant-elim attribute
  TypeNode t = NodeManager::currentNM()->booleanType();
  Node n_attr = NodeManager::currentNM()->mkSkolem("qe", t, "Auxiliary variable for qe attr.");
  std::vector< Node > node_values;
  d_theoryEngine->setUserAttribute( doFull ? "quant-elim" : "quant-elim-partial", n_attr, node_values, "");
  n_attr = NodeManager::currentNM()->mkNode(kind::INST_ATTRIBUTE, n_attr);
  n_attr = NodeManager::currentNM()->mkNode(kind::INST_PATTERN_LIST, n_attr);
  std::vector< Node > e_children;
  e_children.push_back( n_e[0] );
  e_children.push_back(n_e.getKind() == kind::EXISTS ? n_e[1]
                                                     : n_e[1].negate());
  e_children.push_back( n_attr );
  Node nn_e = NodeManager::currentNM()->mkNode( kind::EXISTS, e_children );
  Trace("smt-qe-debug") << "Query for quantifier elimination : " << nn_e << std::endl;
  Assert( nn_e.getNumChildren()==3 );
  Result r = checkSatisfiability(nn_e.toExpr(), true, true);
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if(r.asSatisfiabilityResult().isSat() != Result::UNSAT ) {
    if( r.asSatisfiabilityResult().isSat() != Result::SAT && doFull ){
      stringstream ss;
      ss << "While performing quantifier elimination, unexpected result : " << r << " for query.";
      InternalError(ss.str().c_str());
    }
    std::vector< Node > inst_qs;
    d_theoryEngine->getInstantiatedQuantifiedFormulas( inst_qs );
    Assert( inst_qs.size()<=1 );
    Node ret_n;
    if( inst_qs.size()==1 ){
      Node top_q = inst_qs[0];
      //Node top_q = Rewriter::rewrite( nn_e ).negate();
      Assert( top_q.getKind()==kind::FORALL );
      Trace("smt-qe") << "Get qe for " << top_q << std::endl;
      ret_n = d_theoryEngine->getInstantiatedConjunction( top_q );
      Trace("smt-qe") << "Returned : " << ret_n << std::endl;
      if (n_e.getKind() == kind::EXISTS)
      {
        ret_n = Rewriter::rewrite(ret_n.negate());
      }
    }else{
      ret_n = NodeManager::currentNM()->mkConst(n_e.getKind() != kind::EXISTS);
    }
    // do extended rewrite to minimize the size of the formula aggressively
    theory::quantifiers::ExtendedRewriter extr(true);
    ret_n = extr.extendedRewrite(ret_n);
    return ret_n.toExpr();
  }else {
    return NodeManager::currentNM()
        ->mkConst(n_e.getKind() == kind::EXISTS)
        .toExpr();
  }
}

void SmtEngine::getInstantiatedQuantifiedFormulas( std::vector< Expr >& qs ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    std::vector< Node > qs_n;
    d_theoryEngine->getInstantiatedQuantifiedFormulas( qs_n );
    for( unsigned i=0; i<qs_n.size(); i++ ){
      qs.push_back( qs_n[i].toExpr() );
    }
  }else{
    Assert( false );
  }
}

void SmtEngine::getInstantiations( Expr q, std::vector< Expr >& insts ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    std::vector< Node > insts_n;
    d_theoryEngine->getInstantiations( Node::fromExpr( q ), insts_n );
    for( unsigned i=0; i<insts_n.size(); i++ ){
      insts.push_back( insts_n[i].toExpr() );
    }
  }else{
    Assert( false );
  }
}

void SmtEngine::getInstantiationTermVectors( Expr q, std::vector< std::vector< Expr > >& tvecs ) {
  SmtScope smts(this);
  Assert(options::trackInstLemmas());
  if( d_theoryEngine ){
    std::vector< std::vector< Node > > tvecs_n;
    d_theoryEngine->getInstantiationTermVectors( Node::fromExpr( q ), tvecs_n );
    for( unsigned i=0; i<tvecs_n.size(); i++ ){
      std::vector< Expr > tvec;
      for( unsigned j=0; j<tvecs_n[i].size(); j++ ){
        tvec.push_back( tvecs_n[i][j].toExpr() );
      }
      tvecs.push_back( tvec );
    }
  }else{
    Assert( false );
  }
}

vector<Expr> SmtEngine::getAssertions() {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssertionsCommand();
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!options::produceAssertions()) {
    const char* msg =
      "Cannot query the current assertion list when not in produce-assertions mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  // copy the result out
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

void SmtEngine::push()
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT push()" << endl;
  d_private->notifyPush();
  d_private->processAssertions();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PushCommand();
  }
  if(!options::incrementalSolving()) {
    throw ModalException("Cannot push when not solving incrementally (use --incremental)");
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // The problem isn't really "extended" yet, but this disallows
  // get-model after a push, simplifying our lives somewhat and
  // staying symmtric with pop.
  setProblemExtended(true);

  d_userLevels.push_back(d_userContext->getLevel());
  internalPush();
  Trace("userpushpop") << "SmtEngine: pushed to level "
                       << d_userContext->getLevel() << endl;
}

void SmtEngine::pop() {
  SmtScope smts(this);
  finalOptionsAreSet();
  Trace("smt") << "SMT pop()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PopCommand();
  }
  if(!options::incrementalSolving()) {
    throw ModalException("Cannot pop when not solving incrementally (use --incremental)");
  }
  if(d_userLevels.size() == 0) {
    throw ModalException("Cannot pop beyond the first user frame");
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // The problem isn't really "extended" yet, but this disallows
  // get-model after a pop, simplifying our lives somewhat.  It might
  // not be strictly necessary to do so, since the pops occur lazily,
  // but also it would be weird to have a legally-executed (get-model)
  // that only returns a subset of the assignment (because the rest
  // is no longer in scope!).
  setProblemExtended(true);

  AlwaysAssert(d_userContext->getLevel() > 0);
  AlwaysAssert(d_userLevels.back() < d_userContext->getLevel());
  while (d_userLevels.back() < d_userContext->getLevel()) {
    internalPop(true);
  }
  d_userLevels.pop_back();

  // Clear out assertion queues etc., in case anything is still in there
  d_private->notifyPop();

  Trace("userpushpop") << "SmtEngine: popped to level "
                       << d_userContext->getLevel() << endl;
  // FIXME: should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SmtEngine::internalPush() {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPush()" << endl;
  doPendingPops();
  if(options::incrementalSolving()) {
    d_private->processAssertions();
    TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
    d_userContext->push();
    // the d_context push is done inside of the SAT solver
    d_propEngine->push();
  }
}

void SmtEngine::internalPop(bool immediate) {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPop()" << endl;
  if(options::incrementalSolving()) {
    ++d_pendingPops;
  }
  if(immediate) {
    doPendingPops();
  }
}

void SmtEngine::doPendingPops() {
  Assert(d_pendingPops == 0 || options::incrementalSolving());
  while(d_pendingPops > 0) {
    TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
    d_propEngine->pop();
    // the d_context pop is done inside of the SAT solver
    d_userContext->pop();
    --d_pendingPops;
  }
}

void SmtEngine::reset()
{
  SmtScope smts(this);
  ExprManager *em = d_exprManager;
  Trace("smt") << "SMT reset()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ResetCommand();
  }
  Options opts;
  opts.copyValues(d_originalOptions);
  this->~SmtEngine();
  NodeManager::fromExprManager(em)->getOptions().copyValues(opts);
  new(this) SmtEngine(em);
}

void SmtEngine::resetAssertions()
{
  SmtScope smts(this);
  doPendingPops();

  Trace("smt") << "SMT resetAssertions()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ResetAssertionsCommand();
  }

  while(!d_userLevels.empty()) {
    pop();
  }

  // Also remember the global push/pop around everything.
  Assert(d_userLevels.size() == 0 && d_userContext->getLevel() == 1);
  d_context->popto(0);
  d_userContext->popto(0);
  DeleteAndClearCommandVector(d_modelGlobalCommands);
  d_userContext->push();
  d_context->push();
}

void SmtEngine::interrupt()
{
  if(!d_fullyInited) {
    return;
  }
  d_propEngine->interrupt();
  d_theoryEngine->interrupt();
}

void SmtEngine::setResourceLimit(unsigned long units, bool cumulative) {
  d_private->getResourceManager()->setResourceLimit(units, cumulative);
}
void SmtEngine::setTimeLimit(unsigned long milis, bool cumulative) {
  d_private->getResourceManager()->setTimeLimit(milis, cumulative);
}

unsigned long SmtEngine::getResourceUsage() const {
  return d_private->getResourceManager()->getResourceUsage();
}

unsigned long SmtEngine::getTimeUsage() const {
  return d_private->getResourceManager()->getTimeUsage();
}

unsigned long SmtEngine::getResourceRemaining() const
{
  return d_private->getResourceManager()->getResourceRemaining();
}

unsigned long SmtEngine::getTimeRemaining() const
{
  return d_private->getResourceManager()->getTimeRemaining();
}

Statistics SmtEngine::getStatistics() const
{
  return Statistics(*d_statisticsRegistry);
}

SExpr SmtEngine::getStatistic(std::string name) const
{
  return d_statisticsRegistry->getStatistic(name);
}

void SmtEngine::safeFlushStatistics(int fd) const {
  d_statisticsRegistry->safeFlushInformation(fd);
}

void SmtEngine::setUserAttribute(const std::string& attr,
                                 Expr expr,
                                 const std::vector<Expr>& expr_values,
                                 const std::string& str_value)
{
  SmtScope smts(this);
  std::vector<Node> node_values;
  for( unsigned i=0; i<expr_values.size(); i++ ){
    node_values.push_back( expr_values[i].getNode() );
  }
  d_theoryEngine->setUserAttribute(attr, expr.getNode(), node_values, str_value);
}

void SmtEngine::setPrintFuncInModel(Expr f, bool p) {
  Trace("setp-model") << "Set printInModel " << f << " to " << p << std::endl;
  for( unsigned i=0; i<d_modelGlobalCommands.size(); i++ ){
    Command * c = d_modelGlobalCommands[i];
    DeclareFunctionCommand* dfc = dynamic_cast<DeclareFunctionCommand*>(c);
    if(dfc != NULL) {
      if( dfc->getFunction()==f ){
        dfc->setPrintInModel( p );
      }
    }
  }
  for( unsigned i=0; i<d_modelCommands->size(); i++ ){
    Command * c = (*d_modelCommands)[i];
    DeclareFunctionCommand* dfc = dynamic_cast<DeclareFunctionCommand*>(c);
    if(dfc != NULL) {
      if( dfc->getFunction()==f ){
        dfc->setPrintInModel( p );
      }
    }
  }
}

void SmtEngine::beforeSearch()
{
  if(d_fullyInited) {
    throw ModalException(
        "SmtEngine::beforeSearch called after initialization.");
  }
}


void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
{
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value);
  }

  if(key == "command-verbosity") {
    if(!value.isAtom()) {
      const vector<SExpr>& cs = value.getChildren();
      if(cs.size() == 2 &&
         (cs[0].isKeyword() || cs[0].isString()) &&
         cs[1].isInteger()) {
        string c = cs[0].getValue();
        const Integer& v = cs[1].getIntegerValue();
        if(v < 0 || v > 2) {
          throw OptionException("command-verbosity must be 0, 1, or 2");
        }
        d_commandVerbosity[c] = v;
        return;
      }
    }
    throw OptionException("command-verbosity value must be a tuple (command-name, integer)");
  }

  if(!value.isAtom()) {
    throw OptionException("bad value for :" + key);
  }

  string optionarg = value.getValue();
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  nodeManagerOptions.setOption(key, optionarg);
}

CVC4::SExpr SmtEngine::getOption(const std::string& key) const
{
  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT getOption(" << key << ")" << endl;

  if(key.length() >= 18 &&
     key.compare(0, 18, "command-verbosity:") == 0) {
    map<string, Integer>::const_iterator i = d_commandVerbosity.find(key.c_str() + 18);
    if(i != d_commandVerbosity.end()) {
      return SExpr((*i).second);
    }
    i = d_commandVerbosity.find("*");
    if(i != d_commandVerbosity.end()) {
      return SExpr((*i).second);
    }
    return SExpr(Integer(2));
  }

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key);
  }

  if(key == "command-verbosity") {
    vector<SExpr> result;
    SExpr defaultVerbosity;
    for(map<string, Integer>::const_iterator i = d_commandVerbosity.begin();
        i != d_commandVerbosity.end();
        ++i) {
      vector<SExpr> v;
      v.push_back(SExpr((*i).first));
      v.push_back(SExpr((*i).second));
      if((*i).first == "*") {
        // put the default at the end of the SExpr
        defaultVerbosity = SExpr(v);
      } else {
        result.push_back(SExpr(v));
      }
    }
    // put the default at the end of the SExpr
    if(!defaultVerbosity.isAtom()) {
      result.push_back(defaultVerbosity);
    } else {
      // ensure the default is always listed
      vector<SExpr> v;
      v.push_back(SExpr("*"));
      v.push_back(SExpr(Integer(2)));
      result.push_back(SExpr(v));
    }
    return SExpr(result);
  }

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  return SExpr::parseAtom(nodeManagerOptions.getOption(key));
}

void SmtEngine::setReplayStream(ExprStream* replayStream) {
  AlwaysAssert(!d_fullyInited,
               "Cannot set replay stream once fully initialized");
  d_replayStream = replayStream;
}

bool SmtEngine::getExpressionName(Expr e, std::string& name) const {
  return d_private->getExpressionName(e, name);
}

void SmtEngine::setExpressionName(Expr e, const std::string& name) {
  Trace("smt-debug") << "Set expression name " << e << " to " << name << std::endl;
  d_private->setExpressionName(e,name);
}

}/* CVC4 namespace */
