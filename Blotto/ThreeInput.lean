import Blotto.ThreeGeometry

/-! Bridge from the original hypotheses of Lemma 2.2 to its transformed
parameters. The a≤d convention is the coordinate swap in the English proof. -/

namespace Blotto

structure ThreeInput where
  B : ℝ
  a : ℝ
  d : ℝ
  c : ℝ
  p : ℝ
  B_pos : 0 < B
  a_pos : 0 < a
  d_pos : 0 < d
  c_pos : 0 < c
  p_pos : 0 < p
  a_le : a ≤ B
  d_le : d ≤ B
  c_le : c ≤ B
  p_le : p ≤ 1
  ordered : a ≤ d
  balance : a + d + p * c = 2 * B

namespace ThreeInput

theorem E_nonnegative (i : ThreeInput) : 0 ≤ i.a + i.d - i.B := by
  have hp := mul_le_mul_of_nonneg_right i.p_le (le_of_lt i.c_pos)
  linarith [i.balance, i.c_le]

noncomputable def geometry (i : ThreeInput) (hE : 0 < i.a + i.d - i.B) : ThreeGeometry where
  u := i.B - i.a
  v := i.B - i.d
  w := i.B - i.c
  h := i.c * (1 - i.p)
  u_pos := by
    have hp := mul_pos i.p_pos i.c_pos
    nlinarith [i.balance, i.ordered, i.d_le]
  v_nonneg := sub_nonneg.mpr i.d_le
  w_nonneg := sub_nonneg.mpr i.c_le
  h_nonneg := mul_nonneg (le_of_lt i.c_pos) (sub_nonneg.mpr i.p_le)
  ordered := by linarith [i.ordered]
  a_pos := by nlinarith [i.a_pos, i.balance]
  E_pos := by nlinarith [i.balance]

theorem geometry_matches (i : ThreeInput) (hE : 0 < i.a + i.d - i.B) :
    (i.geometry hE).a = i.a ∧ (i.geometry hE).d = i.d ∧
      (i.geometry hE).c = i.c ∧ (i.geometry hE).budget = i.B ∧
      (i.geometry hE).mixtureProbability = i.p := by
  have ha : (i.geometry hE).a = i.a := by
    dsimp [geometry, ThreeGeometry.a]
    nlinarith [i.balance]
  have hd : (i.geometry hE).d = i.d := by
    dsimp [geometry, ThreeGeometry.d]
    nlinarith [i.balance]
  have hc : (i.geometry hE).c = i.c := by
    dsimp [geometry, ThreeGeometry.c]
    nlinarith [i.balance]
  have hB : (i.geometry hE).budget = i.B := by
    dsimp [geometry, ThreeGeometry.budget]
    nlinarith [i.balance]
  refine ⟨ha, hd, hc, hB, ?_⟩
  unfold ThreeGeometry.mixtureProbability
  rw [hc]
  apply (div_eq_iff (ne_of_gt i.c_pos)).mpr
  dsimp [geometry]
  nlinarith [i.balance]

/-- The E=0 branch is forced to be exactly the exceptional sampler's case. -/
theorem exceptional_case (i : ThreeInput) (hE : i.a + i.d - i.B = 0) :
    i.p = 1 ∧ i.c = i.B ∧ i.a + i.d = i.B := by
  have hp := mul_le_mul_of_nonneg_right i.p_le (le_of_lt i.c_pos)
  have hc : i.c = i.B := by linarith [i.balance, i.c_le]
  have hpc : i.p * i.c = i.c := by linarith [i.balance]
  have hp1 : i.p = 1 := by
    have hz : (i.p - 1) * i.c = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt i.c_pos))
  exact ⟨hp1, hc, by linarith⟩

end ThreeInput
end Blotto
