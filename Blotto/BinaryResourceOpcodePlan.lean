import Blotto.BinaryNormalizationPlan

/-! Actual planned addition and subtraction feed the selected resource update.
The second opcode consumes the returned total once. Both complete preceding
word/trace/source/division records remain exact; reached emissions are returned
for the existing update counter, without replaying old arithmetic producers. -/
namespace Blotto.BinaryResourceOpcodePlan
open BinaryRationalNormalization BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Record := ((SignedWord × Trace) × ℕ) × ℕ

@[irreducible] def pair (first second chosen : SignedWord) : (Record × Record) × ℕ :=
  let total := BinaryNormalizationPlan.apply .add first second
  let other := BinaryNormalizationPlan.apply .sub total.1.1.1.1 chosen
  ((total.1,other.1),total.2+other.2)

theorem pair_compat (first second chosen : SignedWord) :
    (pair first second chosen).1 =
      (BinaryQuadraticMeasured.applyMeasured .add first second,
        BinaryQuadraticMeasured.applyMeasured .sub
          (BinaryQuadraticMeasured.applyMeasured .add first second).1.1.1 chosen) := by
  simp only [pair,BinaryNormalizationPlan.apply_compat]

theorem pair_price (first second chosen : SignedWord) :
    (pair first second chosen).2 ≤
      25*((pair first second chosen).1.1.1.1.2.length+
        (pair first second chosen).1.2.1.1.2.length)+10 := by
  have ht := BinaryNormalizationPlan.apply_price .add first second
  have ho := BinaryNormalizationPlan.apply_price .sub
    (BinaryNormalizationPlan.apply .add first second).1.1.1.1 chosen
  simp only [pair]
  omega

theorem pair_division (first second chosen : SignedWord) :
    (pair first second chosen).1.1.2+(pair first second chosen).1.2.2 ≤
      4*((pair first second chosen).1.1.1.2+(pair first second chosen).1.2.1.2) := by
  have ht := BinaryNormalizationPlan.apply_division .add first second
  have ho := BinaryNormalizationPlan.apply_division .sub
    (BinaryNormalizationPlan.apply .add first second).1.1.1.1 chosen
  simp only [pair]
  omega

end Blotto.BinaryResourceOpcodePlan
