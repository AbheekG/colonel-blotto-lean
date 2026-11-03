import Blotto.ThreeCoupling

/-! Parameter and branch checks for manuscript Lemma 2.3. These do not yet
certify the averaged conditional law in its first case. -/

namespace Blotto

structure NestedInput where
  M : ℝ
  a : ℝ
  d : ℝ
  c : ℝ
  t : ℝ
  q : ℝ
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

namespace NestedInput

noncomputable def h (i : NestedInput) : ℝ := i.q * (i.c - i.t)
noncomputable def u (i : NestedInput) : ℝ := i.M - i.a
noncomputable def v (i : NestedInput) : ℝ := i.M - i.d

theorem h_pos (i : NestedInput) : 0 < i.h :=
  mul_pos i.q_pos (sub_pos.mpr i.t_lt)

theorem transformed_balance (i : NestedInput) : i.c = i.u + i.v + i.h := by
  dsimp [u, v, h]
  nlinarith [i.balance]

theorem lengths (i : NestedInput) :
    0 ≤ i.v ∧ i.v ≤ i.u ∧ 0 < i.u ∧ i.t < i.u + i.v ∧ i.u + i.v < i.c := by
  have hv : 0 ≤ i.v := sub_nonneg.mpr i.d_le
  have hvu : i.v ≤ i.u := by dsimp [v, u]; linarith [i.ordered]
  have ht : i.t < i.u + i.v := by
    have he := i.transformed_balance
    dsimp [h] at he
    nlinarith [mul_pos (sub_pos.mpr i.q_lt) (sub_pos.mpr i.t_lt)]
  have hc : i.u + i.v < i.c := by linarith [i.transformed_balance, i.h_pos]
  exact ⟨hv, hvu, by linarith [i.t_pos], ht, hc⟩

/-- The same nonnegative vertex parameters used by the three-variable tables. -/
noncomputable def geometry (i : NestedInput) : ThreeGeometry where
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
    dsimp [u, v] at he
    dsimp [v]
    nlinarith [i.a_pos]
  E_pos := add_pos_of_nonneg_of_pos (sub_nonneg.mpr i.c_le) i.h_pos

theorem geometry_matches (i : NestedInput) :
    i.geometry.a = i.a ∧ i.geometry.d = i.d ∧ i.geometry.c = i.c ∧
      i.geometry.budget = i.M := by
  have he := i.transformed_balance
  dsimp [u, v] at he
  dsimp [geometry, ThreeGeometry.a, ThreeGeometry.d, ThreeGeometry.c, ThreeGeometry.budget,
    u, v]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

noncomputable def location (i : NestedInput) (r : ℝ) : ℝ :=
  i.h * i.t * r / (i.h + i.t - i.t * r)

theorem location_denominator (i : NestedInput) {r : ℝ} (hr : r ≤ 1) :
    0 < i.h + i.t - i.t * r := by
  nlinarith [i.h_pos, i.t_pos]

theorem location_bounds (i : NestedInput) {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) :
    0 ≤ i.location r ∧ i.location r ≤ i.t := by
  have hden := i.location_denominator hr.2
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (le_of_lt i.h_pos) (le_of_lt i.t_pos)) hr.1)
      (le_of_lt hden)
  · apply (div_le_iff₀ hden).mpr
    have hn : 0 ≤ (1 - r) * i.t * (i.h + i.t) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hr.2) (le_of_lt i.t_pos))
        (le_of_lt (add_pos i.h_pos i.t_pos))
    nlinarith only [hn]

/-- The inverse CDF of the explicit location transform, on its support. -/
theorem location_threshold (i : NestedInput) {r s : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (hs : 0 ≤ s ∧ s ≤ i.t) :
    i.location r ≤ s ↔ r ≤ s * (i.h + i.t) / (i.t * (i.h + s)) := by
  have hd := i.location_denominator hr.2
  have hsden : 0 < i.t * (i.h + s) := mul_pos i.t_pos (by linarith [i.h_pos])
  rw [location, div_le_iff₀ hd, le_div_iff₀ hsden]
  constructor <;> intro h <;> nlinarith

noncomputable def conditionalProbability (i : NestedInput) (s : ℝ) : ℝ :=
  (i.c - i.h - 2 * s) / (i.c - s)

theorem conditional_bounds (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) :
    0 ≤ i.conditionalProbability s ∧ i.conditionalProbability s ≤ 1 := by
  have hl := i.lengths
  have hcs : 0 < i.c - s := by linarith [i.t_lt]
  have hn : 0 ≤ i.c - i.h - 2 * s := by linarith [i.transformed_balance]
  exact ⟨div_nonneg hn (le_of_lt hcs), (div_le_one hcs).mpr (by linarith [i.h_pos])⟩

/-- Every nonzero conditional branch satisfies all original hypotheses of
Lemma 2.2; no constant-sum coupling is assumed here. -/
noncomputable def conditionalInput (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) : ThreeInput where
  B := i.M - s
  a := i.a
  d := i.d
  c := i.c - s
  p := i.conditionalProbability s
  B_pos := by
    have ht := htv
    dsimp [v] at ht
    linarith [i.d_pos]
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := by linarith [i.t_lt]
  p_pos := hp
  a_le := by have hl := i.lengths; dsimp [u, v] at *; linarith
  d_le := by dsimp [v] at *; linarith
  c_le := by linarith [i.c_le]
  p_le := (i.conditional_bounds htv hs).2
  ordered := i.ordered
  balance := by
    have hcs : i.c - s ≠ 0 := ne_of_gt (by linarith [i.t_lt])
    rw [conditionalProbability, div_mul_cancel₀ _ hcs]
    have he := i.transformed_balance
    dsimp [u, v] at he
    linarith

theorem conditional_zero (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : i.conditionalProbability s = 0) :
    i.u = s ∧ i.v = s ∧ i.a = i.M - s ∧ i.d = i.M - s := by
  have hl := i.lengths
  have hcs : i.c - s ≠ 0 := ne_of_gt (by linarith [i.t_lt])
  have hn : i.c - i.h - 2 * s = 0 := (div_eq_zero_iff.mp hp).resolve_right hcs
  have he := i.transformed_balance
  have hu : i.u = s := by linarith
  have hv : i.v = s := by linarith
  refine ⟨hu, hv, ?_, ?_⟩
  · dsimp [u] at hu; linarith
  · dsimp [v] at hv; linarith

end NestedInput
end Blotto
