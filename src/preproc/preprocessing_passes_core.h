#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H
#define __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H

#include "preproc/preprocessing_pass.h"
#include "theory/substitutions.h"
#include "theory/arith/pseudoboolean_proc.h"
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
  ExpandingDefinitionsPass(ResourceManager* resourceManager, TimerStat definitionExpansionTime);
 private:
  TimerStat d_definitionExpansionTime;
  Node expandDefinitions(TNode n, hash_map<Node, Node, NodeHashFunction>& cache, bool expandOnly);
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
     SimplifyAssertionsPass(ResourceManager* resourceManager, unsigned simplifyAssertionsDepth);
  private:
     unsigned d_simplifyAssertionsDepth;
 
};
 
}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASSES_CORE_H */
