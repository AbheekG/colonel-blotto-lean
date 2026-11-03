import Blotto.GeneralPaperOrderedProfitRows

/-! Concrete instantiation of the native optimizer with the paper's literal
lexicographic response tags. Its actual highest-feasible root uses the closed
budget tag. The output is a complete option-index tuple and achieves eta/2
for actual generated signed-tail profits, with symbolic row feasibility.
Valid code catalogues, physical realization and the adaptive selector remain
separate required source joins.
-/
namespace Blotto.GeneralPaperTaggedNativeOptimizer
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperResponseTagSums
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBuild GeneralPaperOrderedProfitRows
set_option autoImplicit false
set_option maxHeartbeats 3500000

def inputTree {m K : ℕ} (lambda k Qv U : ℕ) (weights : FixedArrayTable m ℕ)
    (summaries values : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) :=
  GeneralPaperOrderedNativeProfitOptimizer.inputTree (GeneralPaperProfitParameters.prepare m lambda k Qv)
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
    (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j)))
    (GeneralPaperOrderedNativeProfitOptimizer.plans k U summaries codes tags)

def optimize {m K k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cachedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (B : ℚ) :=
  GeneralPaperOrderedNativeProfitOptimizer.optimize prepared T weights prefixes cachedPlans (budget B)

theorem native_guarantee {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (summaries values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) (B : ℚ)
    (labels : List (Fin K)) (cost : Tag) (P : ℕ)
    (hRealizes : Realizes (inputTree lambda k Qv U weights summaries values codes tags) labels cost P)
    (hBudget : cost.threshold<B ∨ (cost.threshold=B ∧ cost.opened=false)) :
    ∃ label output,
      optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j)))
        (GeneralPaperOrderedNativeProfitOptimizer.plans k U summaries codes tags) B=some (label,output) ∧
      output.length=2^(GeneralPaperProfitParameters.parameters m lambda k Qv).height ∧
      (let selected := resources (fields (inputTree lambda k Qv U weights summaries values codes tags)) output
       (selected.map Tag.threshold).sum<B ∨ ((selected.map Tag.threshold).sum=B ∧ ∀ a∈selected, a.opened=false)) ∧
      GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf P-
        GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
          (profits (fields (inputTree lambda k Qv U weights summaries values codes tags)) output).sum≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  obtain ⟨label,output,outCost,outProfit,hSolve,hOut,hCost,hProfit⟩ :=
    GeneralPaperOrderedNativeProfitOptimizer.native_guarantee lambda k Qv U hQv weights hWeights summaries values hTotal codes tags
      (budget B) labels cost P hRealizes ((feasible_iff cost B).mpr hBudget)
  change Realizes (inputTree lambda k Qv U weights summaries values codes tags) output outCost outProfit at hOut
  have hLen := realizes_length _ output outCost outProfit hOut
  obtain ⟨hResource,hInputProfit⟩ := realizes_sums _ output outCost outProfit hOut
  refine ⟨label,output,hSolve,hLen,?_,?_⟩
  · apply (sum_feasible_iff _ B).mp
    rw [hResource]
    exact hCost
  · rw [hInputProfit]
    exact hProfit

end Blotto.GeneralPaperTaggedNativeOptimizer
