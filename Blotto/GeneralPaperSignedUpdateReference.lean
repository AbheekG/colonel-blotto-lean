import Blotto.GeneralPaperSignedUpdatePlan

/-! Full signed-code semantics of the actual cached integer update. The
positive-sign codes precede the negative-sign codes. The endpoint and zero
bid cases agree with the retained signed row-minus-CDF variation theorem.
-/
namespace Blotto.GeneralPaperSignedUpdateReference
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def increment (k U bid : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (code : ℕ) : ℕ :=
  GeneralPaperRoundedLosses.signedIncrement (GeneralPaperSourceParameters.prepare k).meshDenominator
    (GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (GeneralPaperSignedUpdatePlan.project U code+1))
    (decide (code<U)) (decide (bid≤GeneralPaperSignedUpdatePlan.project U code))

def loss (k U bid : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (code : ℕ) : ℚ :=
  GeneralPaperRoundedLosses.signedLoss (GeneralPaperSourceParameters.prepare k).meshDenominator
    (GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (GeneralPaperSignedUpdatePlan.project U code+1))
    (decide (code<U)) (decide (bid≤GeneralPaperSignedUpdatePlan.project U code))

theorem evaluate_increment {m : ℕ} (k U bid : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperSignedUpdatePlan.evaluate k U bid preparedPrefix (GeneralPaperSignedUpdatePlan.prepare k U summary codes) q).increment=
      increment k U bid summary preparedPrefix (codes.read q) := GeneralPaperSignedUpdatePlan.evaluate_increment _ _ _ _ _ _ _

theorem increment_loss (k U bid : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (code : ℕ) :
    GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (increment k U bid summary (GeneralPaperEpochPrefixArray.build values) code)=
      loss k U bid summary (GeneralPaperEpochPrefixArray.build values) code := by
  rw [GeneralPaperSourceParameters.theta_mesh]
  exact GeneralPaperRoundedLosses.signed_increment_loss _ _ (GeneralPaperSourceParameters.mesh_positive k)
    (GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _) _ _

theorem loss_real (k U bid : ℕ) (hU : 0<U)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (code : ℕ) :
    (loss k U bid summary preparedPrefix code:ℝ)=
      GeneralPaperLossVariation.signedConcatenation
        (GeneralPaperLossVariation.rowDifference (GeneralPaperPreparedCDFProperties.cdf k summary preparedPrefix) bid) (U-1) code := by
  by_cases hCode : code<U
  · have hLast : code≤U-1 := by omega
    by_cases hHit : bid≤code
    <;> simp [loss,GeneralPaperSignedUpdatePlan.project,hCode,hLast,hHit,
      GeneralPaperRoundedLosses.signedLoss,GeneralPaperLossVariation.signedConcatenation,
      GeneralPaperLossVariation.rowDifference,GeneralPaperLossVariation.indicator,
      GeneralPaperPreparedCDFProperties.cdf,GeneralPaperRankedCDFQuery.referenceValue]
  · have hLast : ¬code≤U-1 := by omega
    have hShift : code-(U-1+1)=code-U := by omega
    by_cases hHit : bid≤code-U
    <;> simp [loss,GeneralPaperSignedUpdatePlan.project,hCode,hLast,hShift,hHit,
      GeneralPaperRoundedLosses.signedLoss,GeneralPaperLossVariation.signedConcatenation,
      GeneralPaperLossVariation.rowDifference,GeneralPaperLossVariation.indicator,
      GeneralPaperPreparedCDFProperties.cdf,GeneralPaperRankedCDFQuery.referenceValue]

theorem loss_variation (k U bid : ℕ) (hU : 0<U) (hBid : bid<U)
    (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hCodes : ∀ r, summary.read r<U) :
    GeneralPaperOrderedVariation.variation
      (fun code => (loss k U bid summary (GeneralPaperEpochPrefixArray.build values) code:ℝ)) (2*U-1)≤4 := by
  have he := GeneralPaperPreparedCDFProperties.signed_variation k U bid summary values hU hBid hMono hTotal hCodes
  have hf : (fun code => (loss k U bid summary (GeneralPaperEpochPrefixArray.build values) code:ℝ))=
      GeneralPaperLossVariation.signedConcatenation
        (GeneralPaperLossVariation.rowDifference (GeneralPaperPreparedCDFProperties.cdf k summary (GeneralPaperEpochPrefixArray.build values)) bid) (U-1) :=
    funext (loss_real k U bid hU summary _)
  rw [hf]
  exact he

theorem executed_variation (k U bid : ℕ) (hU : 0<U) (hBid : bid<U)
    (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hCodes : ∀ r, summary.read r<U) :
    GeneralPaperOrderedVariation.variation
      (fun code => (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (increment k U bid summary (GeneralPaperEpochPrefixArray.build values) code):ℝ)) (2*U-1)≤4 := by
  have he := loss_variation k U bid hU hBid summary values hMono hTotal hCodes
  convert he using 1
  congr 1
  funext code
  rw [increment_loss k U bid summary values hTotal code]

end Blotto.GeneralPaperSignedUpdateReference
