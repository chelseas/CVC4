#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H
#define __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H

#include "preproc/preprocessing_pass.h"
#include "theory/substitutions.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "smt/smt_engine.h"
#include "smt/term_formula_removal.h"
#include "decision/decision_engine.h"

namespace CVC4 {

using namespace theory;

namespace preproc {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
typedef context::CDList<Node> NodeList;

class ExpandingDefinitionsPass : public PreprocessingPass {
 public:   
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  ExpandingDefinitionsPass(SmtEngine* smt, TimerStat definitionExpansionTime);
 private:
  SmtEngine* d_smt;
  TimerStat d_definitionExpansionTime;
  Node expandDefinitions(TNode n, NodeToNodeHashMap& cache,
                         bool expandOnly = false)
      throw(TypeCheckingException, LogicException, UnsafeInterruptException);
};
 
class NlExtPurifyPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  NlExtPurifyPass();

 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

// TODO: Create a static instance of each pass.
static NlExtPurifyPass nlExtPurifyPass;

class CEGuidedInstPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  CEGuidedInstPass(TheoryEngine* theoryEngine);
 private:
  TheoryEngine* d_theoryEngine;
};
 
class SolveRealAsIntPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  SolveRealAsIntPass();
 private:
  Node realToInt(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

class SolveIntAsBVPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  SolveIntAsBVPass();
 private:
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeMap& cache); 
};

class BitBlastModePass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   BitBlastModePass(TheoryEngine* theoryEngine); 
 private:
   TheoryEngine* d_theoryEngine;
};

class BVAbstractionPass : public PreprocessingPass {
 public: 
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  BVAbstractionPass(SmtEngine* smt, TheoryEngine* theoryEngine);
 private:
  SmtEngine* d_smt;
  TheoryEngine* d_theoryEngine;
  // Abstract common structure over small domains to UF
  // return true if changes were made.
  void bvAbstraction(AssertionPipeline* assertionsToPreprocess);  
};

class UnconstrainedSimpPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  UnconstrainedSimpPass(TimerStat unconstrainedSimpTime, TheoryEngine* theoryEngine);
 private:
  TimerStat d_unconstrainedSimpTime;
  TheoryEngine* d_theoryEngine;
  // Simplify based on unconstrained values
};

class RewritePass : public PreprocessingPass {
 public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    RewritePass();
};
 
class NotUnsatCoresPass : public PreprocessingPass {
 public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    NotUnsatCoresPass(theory::SubstitutionMap* topLevelSubstitutions);
 private:
    theory::SubstitutionMap* d_topLevelSubstitutions;
};
 
class BVToBoolPass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   BVToBoolPass(TheoryEngine* theoryEngine);
 private:
  // Lift bit-vectors of size 1 to booleans
  TheoryEngine* d_theoryEngine;
  void bvToBool(AssertionPipeline* assertionsToPreprocess);
};

class BoolToBVPass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsTopreprocess);
   BoolToBVPass(TheoryEngine* theoryEngine);
 private:
   // Convert booleans to bit-vectors of size 1
  TheoryEngine* d_theoryEngine;
  void boolToBv(AssertionPipeline* assertionsToPreprocess);
};

class SepPreSkolemEmpPass : public PreprocessingPass {
  public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   SepPreSkolemEmpPass();
};

class QuantifiedPass : public PreprocessingPass {
  public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    QuantifiedPass(TheoryEngine* theoryEngine, SmtEngine* smt);
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

class InferenceOrFairnessPass : public PreprocessingPass {
  public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    InferenceOrFairnessPass(TheoryEngine* theoryEngine, SmtEngine* smt);
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

class PBRewritePass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     PBRewritePass(theory::arith::PseudoBooleanProcessor* pbsProcessor);
  private:
    theory::arith::PseudoBooleanProcessor* d_pbsProcessor;  
};

class RemoveITEPass : public PreprocessingPass {
  public: 
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     RemoveITEPass(SmtEngine* smt, IteSkolemMap* iteSkolemMap, RemoveTermFormulas* iteRemover);
  private:
     SmtEngine* d_smt;
     IteSkolemMap* d_iteSkolemMap;
     RemoveTermFormulas* d_iteRemover;
};
 
class DoStaticLearningPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     DoStaticLearningPass(TheoryEngine* theoryEngine, SmtEngine* smt, TimerStat staticLearningTime);
  private:
     TheoryEngine* d_theoryEngine;
     SmtEngine* d_smt;
     TimerStat d_staticLearningTime;
     //Performs static learning on the assertions.
     void staticLearning(AssertionPipeline* assertionsToPreprocess);
};

class RewriteApplyToConstPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     RewriteApplyToConstPass(TimerStat rewriteApplyToConstTime);
  private:
    TimerStat d_rewriteApplyToConstTime;
    Node rewriteApplyToConst(TNode n);
};

class TheoryPreprocessPass : public PreprocessingPass {
  public :
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      TheoryPreprocessPass(TheoryEngine* theoryEngine, TimerStat theoryPreprocessTime);
  private:
      TheoryEngine* d_theoryEngine;
      TimerStat d_theoryPreprocessTime;
};
 
class BitBlastModeEagerPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     BitBlastModeEagerPass(TheoryEngine* theoryEngine);
  private:
     TheoryEngine* d_theoryEngine;
}; 

class NoConflictPass : public PreprocessingPass {
  public:
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      NoConflictPass(DecisionEngine* decisionEngine, unsigned realAssertionsEnd, IteSkolemMap* iteSkolemMap );
  private:
     DecisionEngine* d_decisionEngine;
     unsigned d_realAssertionsEnd;
     IteSkolemMap* d_iteSkolemMap;
}; 

class CNFPass : public PreprocessingPass{
  public:
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      CNFPass(prop::PropEngine* propEngine, TimerStat cnfConversionTime);
  private:
     prop::PropEngine* d_propEngine; 
     TimerStat d_cnfConversionTime;
};

class RepeatSimpPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     RepeatSimpPass(theory::SubstitutionMap* topLevelSubstitutions, unsigned simplifyAssertionsDepth, bool* noConflict, IteSkolemMap iteSkolemMap, unsigned realAssertionsEnd);
  private: 
     theory::SubstitutionMap* d_topLevelSubstitutions;
     void collectSkolems(TNode n, set<TNode>& skolemSet, unordered_map<Node, bool, NodeHashFunction>& cache);
     bool checkForBadSkolems(TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache);
     unsigned d_simplifyAssertionsDepth;
     bool* noConflict;
     IteSkolemMap d_iteSkolemMap;
     unsigned d_realAssertionsEnd;
};     

class NonClausalSimplificationPass : public PreprocessingPass{
  public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    NonClausalSimplificationPass(SmtEngine* smt, bool* propagatorNeedsFinish, theory::booleans::CircuitPropagator* propagator, TimerStat nonclausalSimplificationTime, context::CDO<unsigned>* substitutionsIndex, theory::SubstitutionMap* topLevelSubstitutions, std::vector<Node>* nonClausalLearnedLiterals, IntStat numConstantProps, Node dtrue, unsigned realAssertionsEnd); 

  private:
   SmtEngine* d_smt;
   bool* d_propagatorNeedsFinish;
   theory::booleans::CircuitPropagator* d_propagator;
   TimerStat d_nonclausalSimplificationTime;
   context::CDO<unsigned>* d_substitutionsIndex;
   theory::SubstitutionMap* d_topLevelSubstitutions;
   std::vector<Node>* d_nonClausalLearnedLiterals;
   IntStat d_numConstantProps;//Do I need to pass in a pointer for this?
   unsigned d_realAssertionsEnd;
};

class MiplibTrickPass : public PreprocessingPass {
  public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   MiplibTrickPass(SmtEngine* smt, TimerStat miplibPassTime, theory::booleans::CircuitPropagator* propagator, std::vector<Node>* boolsVars, unsigned realAssertionsEnd, Node dtrue, IntStat numMiplibAssertionsRemoved, theory::SubstitutionMap* topLevelSubstitutions, context::Context* fakeContext); 
  private:
   SmtEngine* d_smt;
   TimerStat d_miplibPassTime;
   theory::booleans::CircuitPropagator* d_propagator;
   std::vector<Node>* d_boolVars;
   unsigned d_realAssertionsEnd;
   IntStat d_numMiplibAssertionsRemoved;  
   theory::SubstitutionMap* d_topLevelSubstitutions;
   context::Context* d_fakeContext;
   
   void traceBackToAssertions(const std::vector<Node>& nodes,
                             std::vector<TNode>& assertions);
   void doMiplibTrick(AssertionPipeline* assertionsToPreprocess);
   size_t removeFromConjunction(Node& n ,const std::unordered_set<unsigned long>& toRemove);
};

class EarlyTheoryPass : public PreprocessingPass {
 public: 
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   EarlyTheoryPass(TheoryEngine* theoryEngine, TimerStat theoryPreprocessTime);
 private:
   TheoryEngine* d_theoryEngine;
   TimerStat d_theoryPreprocessTime;
};

class SimpITEPass : public PreprocessingPass {
  public: 
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   SimpITEPass(unsigned realAssertionsEnd, TimerStat simpITETime, TheoryEngine* theoryEngine);
 
  private:
   unsigned d_realAssertionsEnd;
   TimerStat d_simpITETime;
   TheoryEngine* d_theoryEngine;

   void compressBeforeRealAssertions(size_t before, AssertionPipeline* assertionsToPreprocess);
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
