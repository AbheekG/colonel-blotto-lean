import Blotto.GeneralPaperSignedTailProperties

/-! The actual paired tail output has the signed value used in objectives
and loss updates. Both interval counts use one global denominator.
-/
namespace Blotto.GeneralPaperSignedTailValues
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def value (k : ℕ) (pair : GeneralPaperSignedTailPlan.Pair) : ℚ :=
  GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.positive-
    GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.negative

theorem evaluate_value {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    value k (GeneralPaperSignedTailPlan.evaluate k preparedPrefix (GeneralPaperSignedTailPlan.prepare k U summary queries) q)=
      GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix (queries.read q) := by
  unfold value GeneralPaperSignedTailProperties.signedValue GeneralPaperSignedTailProperties.tailValue
    GeneralPaperRankedInterval.referenceValue
  rw [GeneralPaperSignedTailPlan.evaluate_positive,GeneralPaperSignedTailPlan.evaluate_negative]
  simp only [Nat.zero_add,two_mul]

theorem evaluate_bounds {m : ℕ} (k U : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values)
      (GeneralPaperSignedTailPlan.prepare k U summary queries) q).positive≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
    (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values)
      (GeneralPaperSignedTailPlan.prepare k U summary queries) q).negative≤(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [GeneralPaperSignedTailPlan.evaluate_positive,GeneralPaperSignedTailPlan.evaluate_negative]
  exact ⟨GeneralPaperRankedInterval.count_bound k summary values hTotal _ _,GeneralPaperRankedInterval.count_bound k summary values hTotal _ _⟩

theorem evaluate_magnitude {m : ℕ} (k U : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    |value k (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values)
      (GeneralPaperSignedTailPlan.prepare k U summary queries) q)|≤1 := by
  rw [evaluate_value]
  exact GeneralPaperSignedTailProperties.signed_magnitude k U summary values hTotal (queries.read q)

theorem error_from_components (k : ℕ) (pair : GeneralPaperSignedTailPlan.Pair) (truePos trueNeg error : ℝ)
    (hp : |truePos-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.positive:ℝ)|≤error)
    (hn : |trueNeg-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator pair.negative:ℝ)|≤error) :
    |(truePos-trueNeg)-(value k pair:ℝ)|≤2*error := by
  have hl := abs_le.mp hp
  have hh := abs_le.mp hn
  unfold value
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

end Blotto.GeneralPaperSignedTailValues
