import Blotto.RationalNestedInput
import Blotto.NestedFamily

/-! Native fixed-mean subfamily parameters. Changing the short interval
length preserves the budget and the original first two lengths. -/

namespace Blotto

theorem NestedInput.eq_of_data (i j : NestedInput) (hM : i.M = j.M) (ha : i.a = j.a)
    (hd : i.d = j.d) (hc : i.c = j.c) (ht : i.t = j.t) (hq : i.q = j.q) : i = j := by
  cases i
  cases j
  cases hM
  cases ha
  cases hd
  cases hc
  cases ht
  cases hq
  rfl

namespace RationalNestedInput

def familyProbability (i : RationalNestedInput) (x : ℚ) : ℚ := i.h / (i.c - x)

theorem familyProbability_real (i : RationalNestedInput) (x : ℚ) :
    (i.familyProbability x : ℝ) = i.real.familyProbability x := by
  simp only [familyProbability, Rat.cast_div, Rat.cast_sub, i.h_real]
  rfl

theorem familyProbability_bounds (i : RationalNestedInput) {x : ℚ} (hx : x < i.u + i.v) :
    0 < i.familyProbability x ∧ i.familyProbability x < 1 := by
  have hxR : (x : ℝ) < i.real.u + i.real.v := by
    rw [← i.u_real, ← i.v_real]
    exact_mod_cast hx
  have h := i.real.familyProbability_bounds hxR
  rw [← i.familyProbability_real] at h
  exact_mod_cast h

theorem fixed_mean_identity (i : RationalNestedInput) : i.a + i.d + i.c - i.h = 2 * i.M := by
  dsimp [h]
  nlinarith [i.balance]

def atLength (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hx : x < i.u + i.v) : RationalNestedInput where
  M := i.M
  a := i.a
  d := i.d
  c := i.c
  t := x
  q := i.familyProbability x
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.c_pos
  t_pos := hx0
  t_lt := lt_trans hx i.lengths.2.2.2.2
  q_pos := (i.familyProbability_bounds hx).1
  q_lt := (i.familyProbability_bounds hx).2
  a_le := i.a_le
  d_le := i.d_le
  c_le := i.c_le
  ordered := i.ordered
  balance := by
    have hd : i.c - x ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hx i.lengths.2.2.2.2))
    have he := congrArg (fun y : ℚ => y * (i.c - x)) i.fixed_mean_identity
    dsimp [familyProbability]
    field_simp [hd]
    nlinarith

theorem atLength_real (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hx : x < i.u + i.v) :
    (i.atLength x hx0 hx).real = i.real.atLength x (by exact_mod_cast hx0)
      (by rw [← i.u_real, ← i.v_real]; exact_mod_cast hx) := by
  apply NestedInput.eq_of_data
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact i.familyProbability_real x

theorem atLength_parameters (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hx : x < i.u + i.v) :
    (i.atLength x hx0 hx).u = i.u ∧ (i.atLength x hx0 hx).v = i.v ∧ (i.atLength x hx0 hx).h = i.h := by
  refine ⟨rfl, rfl, ?_⟩
  change i.h / (i.c - x) * (i.c - x) = i.h
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (lt_trans hx i.lengths.2.2.2.2)))

def geometry (i : RationalNestedInput) : RationalThreeGeometry where
  u := i.u
  v := i.v
  w := i.M - i.c
  h := i.h
  u_pos := i.lengths.2.2.1
  v_nonneg := i.lengths.1
  w_nonneg := sub_nonneg.mpr i.c_le
  h_nonneg := le_of_lt i.h_pos
  ordered := i.lengths.2.1
  a_pos := by
    have he := i.transformed_balance
    dsimp [u, v] at he ⊢
    nlinarith [i.a_pos]
  E_pos := add_pos_of_nonneg_of_pos (sub_nonneg.mpr i.c_le) i.h_pos

theorem geometry_real (i : RationalNestedInput) : i.geometry.real = i.real.geometry := by
  unfold geometry RationalThreeGeometry.real NestedInput.geometry
  simp only [Rat.cast_sub, i.u_real, i.v_real, i.h_real]
  rfl

end RationalNestedInput
end Blotto
