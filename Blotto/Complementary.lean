import Blotto.Translate

/-! A complementary pair and an identically zero third coordinate. -/

namespace Blotto
open MeasureTheory Set

noncomputable def complementaryLaw (B : ℝ) : Mixed 3 :=
  segmentLaw ![0, B, 0] ![B, 0, 0]

theorem complementaryLaw_fullBudget {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ x ∂(complementaryLaw B : Measure (Allocation 3)), FullBudget B x := by
  apply segmentLaw_fullBudget
  · exact fullBudget_three (le_refl 0) hB (le_refl 0) (by ring)
  · exact fullBudget_three hB (le_refl 0) (le_refl 0) (by ring)

theorem complementaryLaw_marginals (B : ℝ) :
    (marginal (complementaryLaw B) 0 : Measure ℝ) = (affineUniform 0 B : Measure ℝ) ∧
    (marginal (complementaryLaw B) 1 : Measure ℝ) = (affineUniform 0 B : Measure ℝ) ∧
    (marginal (complementaryLaw B) 2 : Measure ℝ) = Measure.dirac 0 := by
  simp [complementaryLaw, segmentLaw_marginal, affineUniform_constant]
  rw [affineUniform_reverse B 0]

theorem affineUniform_zero_uniformLaw {a : ℝ} (ha : 0 < a) :
    (affineUniform 0 a : Measure ℝ) = uniformLaw a := by
  rw [affineUniform_increasing ha]
  simp only [intervalLaw, sub_zero, uniformLaw]

/-- Mean two-B and individual bounds force a complementary pair when the
third coordinate has zero mean. -/
theorem complementary_lengths {M a d : ℝ} (haM : a ≤ M) (hdM : d ≤ M)
    (hmean : a + d = 2 * M) : a = M ∧ d = M := by
  constructor <;> linarith

end Blotto
