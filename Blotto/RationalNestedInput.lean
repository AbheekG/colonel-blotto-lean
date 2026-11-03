import Blotto.RationalThreeWeights
import Blotto.NestedFirstGeometry

/-! Native rational parameters for the interior nested-uniform construction.
Its location and conditional table arithmetic have exact real interpretations.
The separate NestedSpec endpoint branches keep their existing scope. -/

namespace Blotto

structure RationalNestedInput where
  M : ℚ
  a : ℚ
  d : ℚ
  c : ℚ
  t : ℚ
  q : ℚ
  a_pos : 0 < a
  d_pos : 0 < d
  c_pos : 0 < c
  t_pos : 0 < t
  t_lt : t < c
  q_pos : 0 < q
  q_lt : q < 1
  a_le : a ≤ M
  d_le : d ≤ M
  c_le : c ≤ M
  ordered : a ≤ d
  balance : a + d + q * t + (1 - q) * c = 2 * M

namespace RationalNestedInput

noncomputable def real (i : RationalNestedInput) : NestedInput where
  M := i.M
  a := i.a
  d := i.d
  c := i.c
  t := i.t
  q := i.q
  a_pos := by exact_mod_cast i.a_pos
  d_pos := by exact_mod_cast i.d_pos
  c_pos := by exact_mod_cast i.c_pos
  t_pos := by exact_mod_cast i.t_pos
  t_lt := by exact_mod_cast i.t_lt
  q_pos := by exact_mod_cast i.q_pos
  q_lt := by exact_mod_cast i.q_lt
  a_le := by exact_mod_cast i.a_le
  d_le := by exact_mod_cast i.d_le
  c_le := by exact_mod_cast i.c_le
  ordered := by exact_mod_cast i.ordered
  balance := by exact_mod_cast i.balance

def h (i : RationalNestedInput) : ℚ := i.q * (i.c - i.t)
def u (i : RationalNestedInput) : ℚ := i.M - i.a
def v (i : RationalNestedInput) : ℚ := i.M - i.d

theorem h_real (i : RationalNestedInput) : (i.h : ℝ) = i.real.h := by simp [h, real, NestedInput.h]
theorem u_real (i : RationalNestedInput) : (i.u : ℝ) = i.real.u := by simp [u, real, NestedInput.u]
theorem v_real (i : RationalNestedInput) : (i.v : ℝ) = i.real.v := by simp [v, real, NestedInput.v]

theorem h_pos (i : RationalNestedInput) : 0 < i.h := mul_pos i.q_pos (sub_pos.mpr i.t_lt)

theorem transformed_balance (i : RationalNestedInput) : i.c = i.u + i.v + i.h := by
  dsimp [u, v, h]
  nlinarith [i.balance]

theorem lengths (i : RationalNestedInput) :
    0 ≤ i.v ∧ i.v ≤ i.u ∧ 0 < i.u ∧ i.t < i.u + i.v ∧ i.u + i.v < i.c := by
  have hr := i.real.lengths
  rw [← i.u_real, ← i.v_real] at hr
  dsimp only [real] at hr
  exact_mod_cast hr

def location (i : RationalNestedInput) (r : ℚ) : ℚ := i.h * i.t * r / (i.h + i.t - i.t * r)

theorem location_real (i : RationalNestedInput) (r : ℚ) : (i.location r : ℝ) = i.real.location r := by
  simp only [location, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, i.h_real]
  rfl

theorem location_bounds (i : RationalNestedInput) {r : ℚ} (hr : 0 ≤ r ∧ r ≤ 1) :
    0 ≤ i.location r ∧ i.location r ≤ i.t := by
  have hrR : (0 : ℝ) ≤ r ∧ (r : ℝ) ≤ 1 := by exact_mod_cast hr
  have hl := i.real.location_bounds hrR
  rw [← i.location_real] at hl
  dsimp only [real] at hl
  exact_mod_cast hl

def conditionalProbability (i : RationalNestedInput) (s : ℚ) : ℚ := (i.c - i.h - 2 * s) / (i.c - s)

theorem conditionalProbability_real (i : RationalNestedInput) (s : ℚ) :
    (i.conditionalProbability s : ℝ) = i.real.conditionalProbability s := by
  simp only [conditionalProbability, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, i.h_real]
  rfl

theorem conditional_bounds (i : RationalNestedInput) (htv : i.t ≤ i.v) {s : ℚ} (hs : 0 ≤ s ∧ s ≤ i.t) :
    0 ≤ i.conditionalProbability s ∧ i.conditionalProbability s ≤ 1 := by
  have htR : i.real.t ≤ i.real.v := by
    rw [← i.v_real]
    change (i.t : ℝ) ≤ (i.v : ℝ)
    exact_mod_cast htv
  have hsR : (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ i.real.t := by
    change (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ (i.t : ℝ)
    exact_mod_cast hs
  have hb := i.real.conditional_bounds htR hsR
  rw [← i.conditionalProbability_real] at hb
  exact_mod_cast hb

def firstGeometry (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) : RationalThreeGeometry where
  u := i.u - s
  v := i.v - s
  w := i.M - i.c
  h := i.h + s
  u_pos := by
    have hcs : 0 < i.c - s := by linarith [i.t_lt]
    have hnum : 0 < i.c - i.h - 2 * s := (div_pos_iff.mp hp).resolve_right
      (fun h => not_lt_of_ge (le_of_lt hcs) h.2) |>.1
    linarith [i.transformed_balance, i.lengths.2.1]
  v_nonneg := by linarith
  w_nonneg := sub_nonneg.mpr i.c_le
  h_nonneg := add_nonneg (le_of_lt i.h_pos) hs.1
  ordered := by linarith [i.lengths.2.1]
  a_pos := by
    have he := i.transformed_balance
    dsimp [u, v] at he ⊢
    nlinarith [i.a_pos]
  E_pos := add_pos_of_nonneg_of_pos (sub_nonneg.mpr i.c_le) (add_pos_of_pos_of_nonneg i.h_pos hs.1)

theorem firstGeometry_real (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) :
    (i.firstGeometry htv s hs hp).real = i.real.firstGeometry
      (by rw [← i.v_real]; change (i.t : ℝ) ≤ (i.v : ℝ); exact_mod_cast htv) s
      (by change (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ (i.t : ℝ); exact_mod_cast hs)
      (by rw [← i.conditionalProbability_real]; exact_mod_cast hp) := by
  unfold firstGeometry RationalThreeGeometry.real NestedInput.firstGeometry
  simp only [Rat.cast_sub, Rat.cast_add, i.u_real, i.v_real, i.h_real]
  rfl

end RationalNestedInput
end Blotto
