import Blotto.FourInput

/-! Exact scaling and reflected nested-mixture parameters for the atom-
conditioning branch of the four-variable construction. -/

namespace Blotto.FourInput
open MeasureTheory Set

noncomputable def shortFraction (i : FourInput) : ℝ := (1 - i.p) * i.ell / i.S
noncomputable def scaleFraction (i : FourInput) : ℝ := 1 - i.shortFraction
noncomputable def nestedProbability (i : FourInput) : ℝ :=
  i.p * i.ell / (i.S - (1 - i.p) * i.ell)
noncomputable def reflectedBudget (i : FourInput) : ℝ := (i.S - i.p * i.ell) / 2

theorem S_lower (i : FourInput) : (2 - i.p) * i.ell ≤ i.S := by
  dsimp [S]
  nlinarith [i.balance, i.ell_le]

theorem shortFraction_bounds (i : FourInput) : 0 < i.shortFraction ∧ i.shortFraction < 1 := by
  have hS := i.lengths_positive.2.2.2
  have hn := mul_pos (sub_pos.mpr i.p_lt) i.ell_pos
  constructor
  · exact div_pos hn hS
  · apply (div_lt_one hS).mpr
    nlinarith [i.S_lower, i.ell_pos]

theorem scaleFraction_bounds (i : FourInput) : 0 < i.scaleFraction ∧ i.scaleFraction < 1 := by
  have hd := i.shortFraction_bounds
  dsimp [scaleFraction]
  constructor <;> linarith

theorem scaleFraction_lower (i : FourInput) : 1 / (2 - i.p) ≤ i.scaleFraction := by
  have hS := i.lengths_positive.2.2.2
  have hD : 0 < 2 - i.p := by linarith [i.p_lt]
  have he : i.scaleFraction = (i.S - (1 - i.p) * i.ell) / i.S := by
    dsimp [scaleFraction, shortFraction]
    field_simp [ne_of_gt hS]
  rw [he]
  apply (div_le_div_iff₀ hD hS).mpr
  have hp : 0 ≤ 1 - i.p := le_of_lt (sub_pos.mpr i.p_lt)
  have ht : 0 ≤ i.S - (2 - i.p) * i.ell := sub_nonneg.mpr i.S_lower
  nlinarith [mul_nonneg hp ht]

theorem scaleFraction_gt_p (i : FourInput) : i.p < i.scaleFraction := by
  have hD : 0 < 2 - i.p := by linarith [i.p_lt]
  have hp : 0 < 1 - i.p := sub_pos.mpr i.p_lt
  have hlt : i.p < 1 / (2 - i.p) := by
    apply (lt_div_iff₀ hD).mpr
    nlinarith [mul_pos hp hp]
  exact lt_of_lt_of_le hlt i.scaleFraction_lower

theorem residual_denominator (i : FourInput) : 0 < i.S - (1 - i.p) * i.ell := by
  nlinarith [i.S_lower, i.ell_pos]

theorem nestedProbability_bounds (i : FourInput) :
    0 < i.nestedProbability ∧ i.nestedProbability < 1 := by
  have hD := i.residual_denominator
  constructor
  · exact div_pos (mul_pos i.p_pos i.ell_pos) hD
  · apply (div_lt_one hD).mpr
    nlinarith [i.S_lower, mul_pos (sub_pos.mpr i.p_lt) i.ell_pos]

theorem scaled_resource_identity (i : FourInput) :
    i.scaleFraction * i.S = i.S - (1 - i.p) * i.ell ∧
      i.nestedProbability * i.scaleFraction * i.S = i.p * i.ell := by
  have hS := ne_of_gt i.lengths_positive.2.2.2
  have hD := ne_of_gt i.residual_denominator
  have he : i.scaleFraction * i.S = i.S - (1 - i.p) * i.ell := by
    dsimp [scaleFraction, shortFraction]
    field_simp [hS]
  refine ⟨he, ?_⟩
  rw [mul_assoc, he, nestedProbability, div_mul_cancel₀ _ hD]

theorem scaled_uniform_bounds (i : FourInput) :
    0 < i.scaleFraction * i.u ∧ 0 < i.scaleFraction * i.v ∧ 0 < i.scaleFraction * i.w ∧
      i.scaleFraction * i.u ≤ i.B ∧ i.scaleFraction * i.v ≤ i.B ∧
      i.scaleFraction * i.w ≤ i.B ∧
      i.scaleFraction * i.u + i.scaleFraction * i.v + i.scaleFraction * i.w + i.ell = 2 * i.B := by
  have hc := i.scaleFraction_bounds
  have hv := i.lengths_positive.1
  have hw := i.lengths_positive.2.1
  have hL : ∀ L : ℝ, 0 ≤ L → L ≤ i.B → i.scaleFraction * L ≤ i.B := by
    intro L hL hLB
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hc.2) hL
    linarith
  refine ⟨mul_pos hc.1 i.u_pos, mul_pos hc.1 hv, mul_pos hc.1 hw,
    hL _ (le_of_lt i.u_pos) (le_trans i.uv (le_trans i.vw i.w_le)),
    hL _ (le_of_lt hv) (le_trans i.vw i.w_le), hL _ (le_of_lt hw) i.w_le, ?_⟩
  have he := i.scaled_resource_identity.1
  dsimp [S] at he
  nlinarith [i.balance]

theorem reflected_budget_bounds (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.w < i.reflectedBudget ∧ i.reflectedBudget = i.S - i.B := by
  have hs := i.small_case_bounds hcase
  dsimp [reflectedBudget]
  constructor
  · linarith [hs.2.2.2.2]
  · have hb := i.balance
    change i.S + i.p * i.ell = 2 * i.B at hb
    linarith

end Blotto.FourInput
