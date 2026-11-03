import Blotto.GeneralPaperNativeRowValues

/-! The executed real-field row maximizes the actual cached weighted rounded
signed-tail score within eta/2. A common zero tag option derives success from
the catalogue's zero entry; no optimizer success or quality oracle is supplied.
-/
namespace Blotto.GeneralPaperNativeRowScore
open scoped BigOperators
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedNativeProfitOptimizer GeneralPaperNativeRowOptimizer GeneralPaperNativeRowValues
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem score_guarantee {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (hK : 0<K) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (summaries values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) (B : ℚ) (comparator : FixedArrayTable m (Fin K))
    (hBudget : resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) comparator≤budget B) :
    ∃ output,
      optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) B=some output ∧
      resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) output≤budget B ∧
      score k Qv weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) comparator-
        score k Qv weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) output≤
          (GeneralPaperSourceParameters.prepare k).eta/2 := by
  obtain ⟨output,hSolve,hCost,hProfit⟩ := native_guarantee lambda k Qv U hQv hK weights hWeights summaries values hTotal codes tags B comparator hBudget
  rw [normalized_profit lambda k Qv U hQv weights summaries values hTotal codes tags comparator,
    normalized_profit lambda k Qv U hQv weights summaries values hTotal codes tags output] at hProfit
  exact ⟨output,hSolve,hCost,by linarith only [hProfit]⟩

theorem zero_success {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (summaries values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) (zeroOption : Fin K) (hZero : ∀ j, (tags.read j).read zeroOption=0)
    (B : ℚ) (hB : 0≤B) :
    ∃ output, optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) B=some output := by
  let zeroRow : FixedArrayTable m (Fin K) := FixedArrayTable.ofFn (fun _ => zeroOption)
  have hBudget : resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) zeroRow≤budget B := by
    rw [resource_tags]
    simp only [zeroRow,FixedArrayTable.read_ofFn,hZero,Finset.sum_const_zero]
    exact budget_nonnegative B hB
  obtain ⟨output,hSolve,_,_⟩ := native_guarantee lambda k Qv U hQv (by have he := zeroOption.isLt; omega)
    weights hWeights summaries values hTotal codes tags B zeroRow hBudget
  exact ⟨output,hSolve⟩

end Blotto.GeneralPaperNativeRowScore
