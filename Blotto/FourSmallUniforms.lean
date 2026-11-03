import Blotto.FourSmallParameters
import Blotto.FourUniforms

/-! The uniform-component branch of the four-variable atom-conditioning case.
Its actual law and every interpolation output spend exactly B. -/

namespace Blotto.FourInput
open MeasureTheory Set

noncomputable def smallUniformInput (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : MergeFourInput where
  B := i.B
  l0 := i.scaleFraction * i.u
  l1 := i.scaleFraction * i.v
  l2 := i.scaleFraction * i.w
  l3 := i.ell
  l0_pos := i.scaled_uniform_bounds.1
  l1_pos := i.scaled_uniform_bounds.2.1
  l2_pos := i.scaled_uniform_bounds.2.2.1
  l3_pos := i.ell_pos
  pair_le := by
    have hc := i.scaleFraction_bounds
    have hw := i.lengths_positive.2.1
    have hcw : i.scaleFraction * i.w ≤ i.w := by
      have he := mul_le_mul_of_nonneg_right (le_of_lt hc.2) (le_of_lt hw)
      simpa only [one_mul] using he
    have hell : i.w < i.ell := by nlinarith [mul_pos i.p_pos i.ell_pos]
    have ha := mul_le_mul_of_nonneg_left (le_trans i.uv i.vw) (le_of_lt hc.1)
    have hb := mul_le_mul_of_nonneg_left i.vw (le_of_lt hc.1)
    have hs := i.scaled_uniform_bounds.2.2.2.2.2.2
    linarith
  l2_le := i.scaled_uniform_bounds.2.2.2.2.2.1
  l3_le := i.ell_le
  balance := i.scaled_uniform_bounds.2.2.2.2.2.2

noncomputable def smallUniformLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : Mixed 4 :=
  (i.smallUniformInput hcase).law

theorem smallUniformLaw_contract (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (∀ᵐ x ∂(i.smallUniformLaw hcase : Measure (Allocation 4)), FullBudget i.B x) ∧
      (marginal (i.smallUniformLaw hcase) 0 : Measure ℝ) = uniformLaw (i.scaleFraction * i.u) ∧
      (marginal (i.smallUniformLaw hcase) 1 : Measure ℝ) = uniformLaw (i.scaleFraction * i.v) ∧
      (marginal (i.smallUniformLaw hcase) 2 : Measure ℝ) = uniformLaw (i.scaleFraction * i.w) ∧
      (marginal (i.smallUniformLaw hcase) 3 : Measure ℝ) = uniformLaw i.ell :=
  (i.smallUniformInput hcase).coupling_contract

theorem smallUniformPoint_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (edge : Fin 9) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget i.B ((i.smallUniformInput hcase).point edge t) :=
  (i.smallUniformInput hcase).point_fullBudget edge ht

end Blotto.FourInput
