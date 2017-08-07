#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H
#define __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H

#include "preproc/preprocessing_pass.h"
#include "smt/smt_engine.h"
#include "smt/term_formula_removal.h"

namespace CVC4 {

using namespace theory;

namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
typedef context::CDList<Node> NodeList;

class ExpandingDefinitionsPass : public PreprocessingPass {
 public:   
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  ExpandingDefinitionsPass(); 
 private:
  SmtEngine* d_smt;
  Node expandDefinitions(TNode n, NodeToNodeHashMap& cache,
                         bool expandOnly = false)
      throw(TypeCheckingException, LogicException, UnsafeInterruptException);
};

static ExpandingDefinitionsPass expandingDefinitionsPass;

class NlExtPurifyPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  NlExtPurifyPass();

 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

static NlExtPurifyPass nlExtPurifyPass;

class CEGuidedInstPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  CEGuidedInstPass();
 private:
  TheoryEngine* d_theoryEngine;
};

static CEGuidedInstPass ceGuidedInstPass;

class SolveRealAsIntPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  SolveRealAsIntPass();
 private:
  Node realToInt(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

static SolveRealAsIntPass solveRealAsIntPass;

class SolveIntAsBVPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  SolveIntAsBVPass();
 private:
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeMap& cache); 
};

static SolveIntAsBVPass solveIntAsBVPass;

class BitBlastModePass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   BitBlastModePass(); 
 private:
   TheoryEngine* d_theoryEngine;
};

static BitBlastModePass bitBlastModePass;

class BVAbstractionPass : public PreprocessingPass {
 public: 
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  BVAbstractionPass();
 private:
  SmtEngine* d_smt;
  TheoryEngine* d_theoryEngine;
  // Abstract common structure over small domains to UF
  // return true if changes were made.
  void bvAbstraction(AssertionPipeline* assertionsToPreprocess);  
};

static BVAbstractionPass bvAbstractionPass;

class UnconstrainedSimpPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
  virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
  UnconstrainedSimpPass();
 private:
  TheoryEngine* d_theoryEngine;
  // Simplify based on unconstrained values
};

static UnconstrainedSimpPass unconstrainedSimpPass;

class RewritePass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
    virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
    RewritePass();
};

static RewritePass rewritePass;

class NotUnsatCoresPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
    virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
    NotUnsatCoresPass();
 private:
    theory::SubstitutionMap* d_topLevelSubstitutions;
};

static NotUnsatCoresPass notUnsatCoresPass;

class BVToBoolPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   BVToBoolPass();
 private:
  // Lift bit-vectors of size 1 to booleans
  TheoryEngine* d_theoryEngine;
  void bvToBool(AssertionPipeline* assertionsToPreprocess);
};

static BVToBoolPass bvToBoolPass;

class BoolToBVPass : public PreprocessingPass {
 public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsTopreprocess);
   BoolToBVPass();
 private:
   // Convert booleans to bit-vectors of size 1
  TheoryEngine* d_theoryEngine;
  void boolToBv(AssertionPipeline* assertionsToPreprocess);
};

static BoolToBVPass boolToBVPass;

class SepPreSkolemEmpPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   SepPreSkolemEmpPass();
};

static SepPreSkolemEmpPass sepPreSkolemEmpPass;

class QuantifiedPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
    virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
    QuantifiedPass();
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

static QuantifiedPass quantifiedPass;

class InferenceOrFairnessPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
    virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
    InferenceOrFairnessPass();
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

static InferenceOrFairnessPass inferenceOrFairnessPass;

class PBRewritePass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     PBRewritePass();
  private:
    theory::arith::PseudoBooleanProcessor* d_pbsProcessor;  
};

static PBRewritePass pbRewritePass;

class RemoveITEPass : public PreprocessingPass {
  public: 
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     RemoveITEPass();
  private:
     SmtEngine* d_smt;
     RemoveTermFormulas* d_iteRemover;
     IntStat d_numAssertionsPre;
     IntStat d_numAssertionsPost;
};

static RemoveITEPass removeITEPass;

class DoStaticLearningPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     DoStaticLearningPass();
  private:
     TheoryEngine* d_theoryEngine;
     SmtEngine* d_smt;
     //Performs static learning on the assertions.
     void staticLearning(AssertionPipeline* assertionsToPreprocess);
};

static DoStaticLearningPass doStaticLearningPass;

class RewriteApplyToConstPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     RewriteApplyToConstPass();
  private:
    Node rewriteApplyToConst(TNode n);
};

static RewriteApplyToConstPass rewriteApplyToConstPass;

class TheoryPreprocessPass : public PreprocessingPass {
  public :
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
      virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
      TheoryPreprocessPass();
  private:
      TheoryEngine* d_theoryEngine;
};

static TheoryPreprocessPass theoryPreprocessPass;

class BitBlastModeEagerPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     BitBlastModeEagerPass();
  private:
     TheoryEngine* d_theoryEngine;
}; 

static BitBlastModeEagerPass bitBlastModeEagerPass;

class NoConflictPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
      virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
      NoConflictPass();
  private:
     DecisionEngine* d_decisionEngine;
}; 

static NoConflictPass noConflictPass;

class CNFPass : public PreprocessingPass{
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
      virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
      CNFPass();
  private:
     prop::PropEngine* d_propEngine; 
};

static CNFPass cnfPass;

class RepeatSimpPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
     virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
     RepeatSimpPass();
  private: 
     theory::SubstitutionMap* d_topLevelSubstitutions;
     void collectSkolems(TNode n, set<TNode>& skolemSet, unordered_map<Node, bool, NodeHashFunction>& cache, AssertionPipeline* assertionsToPreprocess);
     bool checkForBadSkolems(TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache, AssertionPipeline* assertionsToPreprocess);
};     

static RepeatSimpPass repeatSimpPass;

class NonClausalSimplificationPass : public PreprocessingPass{
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
    virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
    NonClausalSimplificationPass(); 

  private:
   SmtEngine* d_smt;
   bool* d_propagatorNeedsFinish;
   theory::booleans::CircuitPropagator* d_propagator;
   context::CDO<unsigned>* d_substitutionsIndex;
   theory::SubstitutionMap* d_topLevelSubstitutions;
   std::vector<Node>* d_nonClausalLearnedLiterals;
   IntStat d_numConstantProps;//Do I need to pass in a pointer for this?
};

static NonClausalSimplificationPass nonClausalSimplifiicationpass;

class MiplibTrickPass : public PreprocessingPass {
  public:
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   MiplibTrickPass(); 
  private:
   SmtEngine* d_smt;
   theory::booleans::CircuitPropagator* d_propagator;
   std::vector<Node>* d_boolVars;
   IntStat d_numMiplibAssertionsRemoved;  
   theory::SubstitutionMap* d_topLevelSubstitutions;
   context::Context d_fakeContext;
   
   void traceBackToAssertions(const std::vector<Node>& nodes,
                             std::vector<TNode>& assertions);
   void doMiplibTrick(AssertionPipeline* assertionsToPreprocess);
   size_t removeFromConjunction(Node& n ,const std::unordered_set<unsigned long>& toRemove);
};

static MiplibTrickPass miplibTrickPass;

class EarlyTheoryPass : public PreprocessingPass {
 public: 
   virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   EarlyTheoryPass(); 
 private:
   TheoryEngine* d_theoryEngine;
};

static EarlyTheoryPass earlyTheoryPass;

class SimpITEPass : public PreprocessingPass {
  public: 
    virtual void initInternal(SmtEngine* smt, TheoryEngine* theoryEngine, 
     theory::SubstitutionMap* topLevelSubstitutions, 
     theory::arith::PseudoBooleanProcessor* pbsProcessor, 
     RemoveTermFormulas* iteRemover, 
     DecisionEngine* decisionEngine, prop::PropEngine* propEngine, 
     bool* propagatorNeedsFinish, 
     theory::booleans::CircuitPropagator* propagator, 
     std::vector<Node>* boolVars, 
     context::CDO<unsigned>* substitutionsIndex, 
     std::vector<Node>* nonClausalLearnedLiterals);
   virtual PreprocessingPassResult applyInternal(AssertionPipeline* assertionsToPreprocess);
   SimpITEPass();
 
  private:
   TheoryEngine* d_theoryEngine;
   void compressBeforeRealAssertions(size_t before, AssertionPipeline* assertionsToPreprocess);
};

static SimpITEPass simpITEPass;

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
