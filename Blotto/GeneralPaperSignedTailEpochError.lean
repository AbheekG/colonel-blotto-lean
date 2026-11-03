import Blotto.GeneralPaperSignedTailValues

/-! Actual prepared tail pairs approximate both sign intervals and their
signed difference. The proof uses the unrounded CDF estimate, so rounding
costs theta once per sign, with the same complete signed normalization.
-/
namespace Blotto.GeneralPaperSignedTailEpochError
open scoped BigOperators
open GeneralPaperPreparedPowers GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem pair_error {m : ℕ} (U : ℕ) (hU : 0<U) (lambda k start count : ℕ)
    (increment : ℕ → Fin (2*U) → ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (location : Fin (GeneralPaperSourceParameters.prepare k).summarySize → Fin (2*U))
    (hLocation : ∀ r, (location r).val=summary.read r) (hMono : Monotone summary.read)
    (delta : ℕ → FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) increment start (code (by omega : 0<2*U) i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (2*U-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code (by omega : 0<2*U) i)):ℝ)) (2*U-1)≤4)
    (queries : FixedArrayTable m ℕ) (q : Fin m) (hA : queries.read q≤U) :
    let p := fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code (by omega : 0<2*U) i)
    let pair := GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count)
      (GeneralPaperSignedTailPlan.prepare k U summary queries) q
    |GeneralPaperOrderedIntervals.mass p (queries.read q) U-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.positive:ℝ)|≤
        10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) ∧
    |GeneralPaperOrderedIntervals.mass p (U+queries.read q) (2*U)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.negative:ℝ)|≤
        10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hn : 0<2*U := by omega
  have hp := GeneralPaperRawEpochCDF.interval_error hn lambda k start count increment summary location hLocation hMono delta hDelta
    hClose hCount hIncrement hMagnitude hVariation (queries.read q) U hA (by omega)
  have hh := GeneralPaperRawEpochCDF.interval_error hn lambda k start count increment summary location hLocation hMono delta hDelta
    hClose hCount hIncrement hMagnitude hVariation (U+queries.read q) (2*U) (by omega) (le_refl _)
  dsimp only
  rw [GeneralPaperSignedTailPlan.evaluate_positive,GeneralPaperSignedTailPlan.evaluate_negative]
  exact ⟨hp,hh⟩

theorem signed_error {m : ℕ} (k U : ℕ) (p : ℕ → ℝ) (queries : FixedArrayTable m ℕ) (q : Fin m) (hA : queries.read q≤U)
    (pair : GeneralPaperSignedTailPlan.Pair)
    (hp : |GeneralPaperOrderedIntervals.mass p (queries.read q) U-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.positive:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hn : |GeneralPaperOrderedIntervals.mass p (U+queries.read q) (2*U)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.negative:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) :
    |(∑ i∈Finset.range (U-queries.read q), (p (queries.read q+i)-p (U+(queries.read q+i))))-
      (GeneralPaperSignedTailValues.value k pair:ℝ)|≤
      20*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+2*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have he := GeneralPaperSignedTailValues.error_from_components k pair _ _ _ hp hn
  rw [GeneralPaperOrderedIntervals.signed_tail_sum p U (queries.read q) hA] at he
  convert he using 1 <;> ring

end Blotto.GeneralPaperSignedTailEpochError
