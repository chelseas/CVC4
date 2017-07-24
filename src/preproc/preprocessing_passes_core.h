#include "cvc4_public.h"

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
namespace preproc {

typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
typedef std::hash_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
typedef context::CDList<Node> NodeList;

class ExpandingDefinitionsPass : public PreprocessingPass {
 public:   
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  ExpandingDefinitionsPass(ResourceManager* resourceManager, SmtEngine* smt, TimerStat definitionExpansionTime);
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
  NlExtPurifyPass(ResourceManager* resourceManager);
 private:
  Node purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache,
                     std::vector<Node>& var_eq, bool beneathMult = false);
};

class CEGuidedInstPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  CEGuidedInstPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine);
 private:
  TheoryEngine* d_theoryEngine;
};
 
class SolveRealAsIntPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  SolveRealAsIntPass(ResourceManager* resourceManager);
 private:
  Node realToInt(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

class SolveIntAsBVPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  SolveIntAsBVPass(ResourceManager* resourceManager);
 private:
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeMap& cache); 
};

class BitBlastModePass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   BitBlastModePass(ResourceManager* resourceManager,
      TheoryEngine* theoryEngine); 
 private:
   TheoryEngine* d_theoryEngine;
};

class BVAbstractionPass : public PreprocessingPass {
 public: 
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  BVAbstractionPass(ResourceManager* resourceManager, 
      SmtEngine* smt, TheoryEngine* theoryEngine);
 private:
  SmtEngine* d_smt;
  TheoryEngine* d_theoryEngine;
  // Abstract common structure over small domains to UF
  // return true if changes were made.
  void bvAbstraction(AssertionPipeline* assertionsToPreprocess);  
};

class ConstrainSubtypesPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  ConstrainSubtypesPass(ResourceManager* resourceManager, SmtEngine* smt);
 private:
  SmtEngine* d_smt;
  void constrainSubtypes(TNode n, AssertionPipeline& assertions)
    throw();
};

class UnconstrainedSimpPass : public PreprocessingPass {
 public:
  virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  UnconstrainedSimpPass(ResourceManager* resourceManager, 
      TimerStat unconstrainedSimpTime, TheoryEngine* theoryEngine);
 private:
  TimerStat d_unconstrainedSimpTime;
  TheoryEngine* d_theoryEngine;
  // Simplify based on unconstrained values
};

class RewritePass : public PreprocessingPass {
 public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    RewritePass(ResourceManager* resourceManager);
};
 
class NotUnsatCoresPass : public PreprocessingPass {
 public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    NotUnsatCoresPass(ResourceManager* resourceManager,
       theory::SubstitutionMap* topLevelSubstitutions);
 private:
    theory::SubstitutionMap* d_topLevelSubstitutions;
};
 
class BVToBoolPass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   BVToBoolPass(ResourceManager* resourceManager, 
      TheoryEngine* theoryEngine);
 private:
  // Lift bit-vectors of size 1 to booleans
  TheoryEngine* d_theoryEngine;
  void bvToBool(AssertionPipeline* assertionsToPreprocess);
};

class BoolToBVPass : public PreprocessingPass {
 public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsTopreprocess);
   BoolToBVPass(ResourceManager* resourceManager,
     TheoryEngine* theoryEngine);
 private:
   // Convert booleans to bit-vectors of size 1
  TheoryEngine* d_theoryEngine;
  void boolToBv(AssertionPipeline* assertionsToPreprocess);
};

class SepPreSkolemEmpPass : public PreprocessingPass {
  public:
   virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
   SepPreSkolemEmpPass(ResourceManager* resourceManager);
};

class QuantifiedPass : public PreprocessingPass {
  public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    QuantifiedPass(ResourceManager* resourceManager, 
      TheoryEngine* theoryEngine, SmtEngine* smt);
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

class InferenceOrFairnessPass : public PreprocessingPass {
  public:
    virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
    InferenceOrFairnessPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt);
  private:
    TheoryEngine* d_theoryEngine;
    SmtEngine* d_smt;
};

class PBRewritePass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     PBRewritePass(ResourceManager* resourceManager, theory::arith::PseudoBooleanProcessor* pbsProcessor);
  private:
    theory::arith::PseudoBooleanProcessor* d_pbsProcessor;  
};

class RemoveITEPass : public PreprocessingPass {
  public: 
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     RemoveITEPass(ResourceManager* resourceManager, SmtEngine* smt, IteSkolemMap* iteSkolemMap, RemoveTermFormulas* iteRemover);
  private:
     SmtEngine* d_smt;
     IteSkolemMap* d_iteSkolemMap;
     RemoveTermFormulas* d_iteRemover;
};
 
class DoStaticLearningPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     DoStaticLearningPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, SmtEngine* smt, TimerStat staticLearningTime);
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
     RewriteApplyToConstPass(ResourceManager* resourceManager, TimerStat rewriteApplyToConstTime);
  private:
    TimerStat d_rewriteApplyToConstTime;
    Node rewriteApplyToConst(TNode n);
};

class TheoryPreprocessPass : public PreprocessingPass {
  public :
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      TheoryPreprocessPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine, TimerStat theoryPreprocessTime);
  private:
      TheoryEngine* d_theoryEngine;
      TimerStat d_theoryPreprocessTime;
};
 
class BitBlastModeEagerPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     BitBlastModeEagerPass(ResourceManager* resourceManager, TheoryEngine* theoryEngine);
  private:
     TheoryEngine* d_theoryEngine;
}; 

class NoConflictPass : public PreprocessingPass {
  public:
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      NoConflictPass(ResourceManager* resourceManager, DecisionEngine* decisionEngine, unsigned realAssertionsEnd, IteSkolemMap* iteSkolemMap );
  private:
     DecisionEngine* d_decisionEngine;
     unsigned d_realAssertionsEnd;
     IteSkolemMap* d_iteSkolemMap;
}; 

class CNFPass : public PreprocessingPass{
  public:
      virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
      CNFPass(ResourceManager* resourceManager, prop::PropEngine* propEngine, TimerStat cnfConversionTime);
  private:
     prop::PropEngine* d_propEngine; 
     TimerStat d_cnfConversionTime;
};

/* 
class RepeatSimpPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
     RepeatSimpPass(ResourceManager* resourceManager, theory::SubstitutionMap* topLevelSubstitutions, unsigned simplifyAssertionsDepth, bool* noConflict, IteSkolemMap iteSkolemMap, unsigned realAssertionsEnd);
  private: 
     theory::SubstitutionMap* d_topLevelSubstitutions;
     void collectSkolems(TNode n, set<TNode>& skolemSet, hash_map<Node, bool, NodeHashFunction>& cache);
     bool checkForBadSkolems(TNode n, TNode skolem, hash_map<Node, bool, NodeHashFunction>& cache);
     bool simplifyAssertions();
     unsigned d_simplifyAssertionsDepth;
     bool* noConflict;
     IteSkolemMap d_iteSkolemMap;
     unsigned d_realAssertionsEnd;
};     

class SimplifyAssertionsPass : public PreprocessingPass {
  public:
     virtual PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess) throw(TypeCheckingException, LogicException,
                                  UnsafeInterruptException);
     SimplifyAssertionsPass(ResourceManager* resourceManager, unsigned simplifyAssertionsDepth, SmtEngine* smt, bool propagatorNeedsFinish, theory::booleans::CircuitPropagator propagator, context::CDO<unsigned> substitutionsIndex, std::vector<Node> nonClausalLearnedLiterals, Node dtrue, TimerStat nonclausalSimplificationTime);
  private:
   unsigned d_simplifyAssertionsDepth;
   SmtEngine* d_smt;
   bool d_propagatorNeedsFinish;
   theory::booleans::CircuitPropagator d_propagator;
   context::CDO<unsigned> d_substitutionsIndex;
   std::vector<Node> d_nonClausalLearnedLiterals;
   Node d_true;
   TimerStat d_nonclausalSimplificationTime;
   bool nonClausalSimplify(AssertionPipeline &d_assertions);
   void addFormula(TNode n, bool inUnsatCore, bool inInput = true, AssertionPipeline d_assertions)
    throw(TypeCheckingException, LogicException);
};
*/
 
}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
