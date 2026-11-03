import Blotto.GeneralPaperSignedUpdateReference

/-! Actual strict and weak CDF pairs inherit their component error from
the constructed rank cache and local-array/power/prefix/mesh pipeline.
-/
namespace Blotto.GeneralPaperCDFPairEpochError
open GeneralPaperPreparedPowers GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem pair_error {n m : ℕ} (hn : 0<n) (lambda k start count : ℕ) (increment : ℕ → Fin n → ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (location : Fin (GeneralPaperSourceParameters.prepare k).summarySize → Fin n)
    (hLocation : ∀ r, (location r).val=summary.read r) (hMono : Monotone summary.read)
    (delta : ℕ → FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (queries : FixedArrayTable m ℕ) (q : Fin m) (hA : queries.read q<n) :
    let p := fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code hn i)
    let pair := GeneralPaperCDFPairPlan.evaluate k (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count)
      (GeneralPaperCDFPairPlan.prepare k summary queries) q
    |prefixMass p (queries.read q)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.lower:ℝ)|≤
        5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) ∧
    |prefixMass p (queries.read q+1)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.upper:ℝ)|≤
        5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hl := GeneralPaperRankedEpochError.cached_error hn lambda k start count increment summary location hLocation hMono delta hDelta hClose
    hCount hIncrement hMagnitude hVariation (GeneralPaperCDFPairPlan.shiftCuts 0 queries).1 q
    (by rw [GeneralPaperCDFPairPlan.shift_read,Nat.add_zero]; omega)
  have hh := GeneralPaperRankedEpochError.cached_error hn lambda k start count increment summary location hLocation hMono delta hDelta hClose
    hCount hIncrement hMagnitude hVariation (GeneralPaperCDFPairPlan.shiftCuts 1 queries).1 q
    (by rw [GeneralPaperCDFPairPlan.shift_read]; omega)
  rw [GeneralPaperCDFPairPlan.shift_read,Nat.add_zero] at hl
  rw [GeneralPaperCDFPairPlan.shift_read] at hh
  exact ⟨hl,hh⟩

end Blotto.GeneralPaperCDFPairEpochError
