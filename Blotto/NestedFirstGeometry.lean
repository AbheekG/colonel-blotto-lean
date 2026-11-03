import Blotto.NestedAverage
import Blotto.MeasurableThree
import Blotto.Translate

/-! The parameter-dependent conditional three-variable couplings in the first
nested case. Numerical parameters and their transport are proved explicitly. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def firstGeometry (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) : ThreeGeometry where
  u := i.u - s
  v := i.v - s
  w := i.M - i.c
  h := i.h + s
  u_pos := by
    have hl := i.lengths
    have hnum : 0 < i.c - i.h - 2 * s := (div_pos_iff.mp hp).resolve_right (by
      have hcs : 0 < i.c - s := by linarith [i.t_lt]
      exact fun h => not_lt_of_ge (le_of_lt hcs) h.2) |>.1
    have he := i.transformed_balance
    linarith
  v_nonneg := by linarith
  w_nonneg := sub_nonneg.mpr i.c_le
  h_nonneg := add_nonneg (le_of_lt i.h_pos) hs.1
  ordered := by linarith [i.lengths.2.1]
  a_pos := by
    have he := i.transformed_balance
    dsimp [u, v] at he
    dsimp [u, v]
    nlinarith [i.a_pos]
  E_pos := add_pos_of_nonneg_of_pos (sub_nonneg.mpr i.c_le) (add_pos_of_pos_of_nonneg i.h_pos hs.1)

theorem firstGeometry_matches (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) :
    (i.firstGeometry htv s hs hp).a = i.a ∧
    (i.firstGeometry htv s hs hp).d = i.d ∧
    (i.firstGeometry htv s hs hp).c = i.c - s ∧
    (i.firstGeometry htv s hs hp).budget = i.M - s ∧
    (i.firstGeometry htv s hs hp).mixtureProbability = i.conditionalProbability s := by
  have he := i.transformed_balance
  have he' := he
  dsimp [u, v] at he'
  have ha : (i.firstGeometry htv s hs hp).a = i.a := by
    dsimp [firstGeometry, ThreeGeometry.a, u, v]; linarith
  have hd : (i.firstGeometry htv s hs hp).d = i.d := by
    dsimp [firstGeometry, ThreeGeometry.d, u, v]; linarith
  have hc : (i.firstGeometry htv s hs hp).c = i.c - s := by
    dsimp [firstGeometry, ThreeGeometry.c]; linarith
  have hB : (i.firstGeometry htv s hs hp).budget = i.M - s := by
    dsimp [firstGeometry, ThreeGeometry.budget, u, v]; linarith
  refine ⟨ha, hd, hc, hB, ?_⟩
  rw [ThreeGeometry.mixtureProbability, hc, conditionalProbability]
  congr 1
  dsimp [firstGeometry]
  linarith

noncomputable def firstPositiveLaw (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) : Mixed 3 :=
  shiftedLaw s (i.firstGeometry htv s hs hp).couplingLaw

theorem firstPositiveLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) :
    ∀ᵐ x ∂(i.firstPositiveLaw htv s hs hp : Measure (Allocation 3)), FullBudget i.M x := by
  have he := i.firstGeometry_matches htv s hs hp
  have hb : (i.firstGeometry htv s hs hp).budget + s = i.M := by linarith [he.2.2.2.1]
  simpa only [firstPositiveLaw, hb] using shiftedLaw_fullBudget hs.1 (i.firstGeometry htv s hs hp).couplingLaw_fullBudget

theorem firstPositiveLaw_marginals (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) :
    (marginal (i.firstPositiveLaw htv s hs hp) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.firstPositiveLaw htv s hs hp) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.firstPositiveLaw htv s hs hp) 2 : Measure ℝ) = i.conditionalThirdLaw s := by
  have he := i.firstGeometry_matches htv s hs hp
  have hm := (i.firstGeometry htv s hs hp).couplingLaw_marginals
  constructor
  · rw [firstPositiveLaw, shiftedLaw_marginal_zero, hm.1, he.1]
  constructor
  · rw [firstPositiveLaw, shiftedLaw_marginal_one, hm.2.1, he.2.1]
  · rw [firstPositiveLaw, shiftedLaw_marginal_two, hm.2.2, he.2.2.1, he.2.2.2.2,
      shift_zeroUniformLaw s i.c (i.conditionalProbability s) (lt_of_le_of_lt hs.2 i.t_lt)]
    rfl

end Blotto.NestedInput
