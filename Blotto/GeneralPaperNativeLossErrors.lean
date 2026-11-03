import Blotto.GeneralPaperCDFPairEpochError

/-! The separately rounded actual component counts enter the selected
integer update with the paper's common 25*nu+3*theta loss error. The local
component estimates are supplied by the preceding CDF/tail epoch theorems.
-/
namespace Blotto.GeneralPaperNativeLossErrors
open scoped BigOperators
open GeneralPaperQueryLossCounts
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def trueLoss (response : Bool) (lo hi pos neg : ℝ) : ℝ :=
  (if response then 0 else 1)-(lo+hi)/2+(pos-neg)

theorem component_error (k : ℕ) (response : Bool) (counts : Counts) (lo hi pos neg : ℝ)
    (hl : |lo-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.lower:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hh : |hi-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.upper:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hp : |pos-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.positive:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hn : |neg-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.negative:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) :
    |trueLoss response lo hi pos neg-(loss k response counts:ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  cases response
  · exact GeneralPaperRoundedLosses.primal_error _ _ _ _ _ _ _ _ _ _ _ hl hh hp hn
  · simpa only [trueLoss,loss,ite_true,zero_sub,neg_div] using
      GeneralPaperRoundedLosses.response_error _ _ _ _ _ _ _ _ _ _ _ hl hh hp hn

theorem executed_error (k : ℕ) (response : Bool) (counts : Counts) (hBounds : Bounds k counts) (lo hi pos neg : ℝ)
    (hl : |lo-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.lower:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hh : |hi-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.upper:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hp : |pos-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.positive:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hn : |neg-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator counts.negative:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) :
    |trueLoss response lo hi pos neg-
      (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment k response counts):ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  rw [increment_loss k response counts hBounds]
  exact component_error k response counts lo hi pos neg hl hh hp hn

theorem evaluate_error {m : ℕ} (k U : ℕ) (response : Bool)
    (cdfSummary tailSummary cdfValues tailValues : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hCDF : 0<∑ r, cdfValues.read r) (hTail : 0<∑ r, tailValues.read r) (queries : FixedArrayTable m ℕ) (q : Fin m)
    (lo hi pos neg : ℝ)
    (hCDFError :
      |lo-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperCDFPairPlan.evaluate k (GeneralPaperEpochPrefixArray.build cdfValues)
          (GeneralPaperCDFPairPlan.prepare k cdfSummary queries) q).lower:ℝ)|≤
        5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) ∧
      |hi-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperCDFPairPlan.evaluate k (GeneralPaperEpochPrefixArray.build cdfValues)
          (GeneralPaperCDFPairPlan.prepare k cdfSummary queries) q).upper:ℝ)|≤
        5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ))
    (hTailError :
      |pos-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build tailValues)
          (GeneralPaperSignedTailPlan.prepare k U tailSummary queries) q).positive:ℝ)|≤
        10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) ∧
      |neg-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build tailValues)
          (GeneralPaperSignedTailPlan.prepare k U tailSummary queries) q).negative:ℝ)|≤
        10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) :
    |trueLoss response lo hi pos neg-
      (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (step k response (GeneralPaperEpochPrefixArray.build cdfValues) (GeneralPaperEpochPrefixArray.build tailValues)
          (prepare k U cdfSummary tailSummary queries) q).1:ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  exact executed_error k response _ (evaluate_bounds k U cdfSummary tailSummary cdfValues tailValues hCDF hTail queries q)
    lo hi pos neg hCDFError.1 hCDFError.2 hTailError.1 hTailError.2

theorem signed_evaluate_error {m : ℕ} (k U bid : ℕ)
    (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (codes : FixedArrayTable m ℕ) (q : Fin m) (trueCDF : ℝ)
    (hError : |trueCDF-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (GeneralPaperSignedUpdatePlan.evaluate k U bid (GeneralPaperEpochPrefixArray.build values)
        (GeneralPaperSignedUpdatePlan.prepare k U summary codes) q).count:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) :
    let result := GeneralPaperSignedUpdatePlan.evaluate k U bid (GeneralPaperEpochPrefixArray.build values)
      (GeneralPaperSignedUpdatePlan.prepare k U summary codes) q
    |(if result.positive then (if result.hit then 1 else 0)-trueCDF else trueCDF-(if result.hit then 1 else 0))-
      (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta result.increment:ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hNu : (0:ℝ)≤(GeneralPaperSourceParameters.prepare k).nu := by
    exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.1.le
  have hTheta : (0:ℝ)≤(GeneralPaperSourceParameters.prepare k).theta := by
    exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.2.le
  let result := GeneralPaperSignedUpdatePlan.evaluate k U bid (GeneralPaperEpochPrefixArray.build values)
    (GeneralPaperSignedUpdatePlan.prepare k U summary codes) q
  have hCount : result.count≤(GeneralPaperSourceParameters.prepare k).meshDenominator := by
    dsimp only [result]
    rw [GeneralPaperSignedUpdatePlan.evaluate_count]
    exact GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _
  have he := GeneralPaperRoundedLosses.signed_error (GeneralPaperSourceParameters.prepare k).meshDenominator result.count trueCDF
    ((GeneralPaperSourceParameters.prepare k).nu:ℝ) ((GeneralPaperSourceParameters.prepare k).theta:ℝ)
    result.positive result.hit hNu hTheta hError
  have hLoss : GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta result.increment=
      GeneralPaperRoundedLosses.signedLoss (GeneralPaperSourceParameters.prepare k).meshDenominator result.count result.positive result.hit := by
    rw [GeneralPaperSourceParameters.theta_mesh]
    exact GeneralPaperRoundedLosses.signed_increment_loss _ _ (GeneralPaperSourceParameters.mesh_positive k) hCount _ _
  change |(if result.positive then (if result.hit then 1 else 0)-trueCDF else trueCDF-(if result.hit then 1 else 0))-
    (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta result.increment:ℝ)|≤ _
  rw [hLoss]
  exact he

end Blotto.GeneralPaperNativeLossErrors
