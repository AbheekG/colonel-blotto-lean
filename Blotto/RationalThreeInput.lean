import Blotto.RationalThreeGeometryCompiler

/-! Original ordered rational inputs compile to the exact three-variable
descriptor, including the exceptional E=0 branch. All arithmetic and branch
comparisons are native rational operations. -/

namespace Blotto
open scoped BigOperators

structure RationalThreeInput where
  B : ℚ
  a : ℚ
  d : ℚ
  c : ℚ
  p : ℚ
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

namespace RationalThreeInput

noncomputable def real (i : RationalThreeInput) : ThreeInput where
  B := i.B
  a := i.a
  d := i.d
  c := i.c
  p := i.p
  B_pos := by exact_mod_cast i.B_pos
  a_pos := by exact_mod_cast i.a_pos
  d_pos := by exact_mod_cast i.d_pos
  c_pos := by exact_mod_cast i.c_pos
  p_pos := by exact_mod_cast i.p_pos
  a_le := by exact_mod_cast i.a_le
  d_le := by exact_mod_cast i.d_le
  c_le := by exact_mod_cast i.c_le
  p_le := by exact_mod_cast i.p_le
  ordered := by exact_mod_cast i.ordered
  balance := by exact_mod_cast i.balance

def geometry (i : RationalThreeInput) (hE : 0 < i.a + i.d - i.B) : RationalThreeGeometry where
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

theorem geometry_real (i : RationalThreeInput) (hE : 0 < i.a + i.d - i.B) :
    (i.geometry hE).real = i.real.geometry (by
      change (0 : ℝ) < (i.a : ℝ) + (i.d : ℝ) - (i.B : ℝ)
      exact_mod_cast hE) := by
  unfold geometry RationalThreeGeometry.real real ThreeInput.geometry
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_one]

def segmentLottery (i : RationalThreeInput) : RationalSegmentLottery 3 9 :=
  if hE : 0 < i.a + i.d - i.B then RationalThreeGeometryCode.compiledLottery (i.geometry hE) else
    ⟨(fun slot => if slot = 0 then 1 else 0), (fun _ => ![0, 0, i.B]), (fun _ => ![i.a, i.d, 0]),
      (by intro slot; split_ifs <;> norm_num), (by simp)⟩

theorem segmentLottery_real (i : RationalThreeInput) : i.segmentLottery.real = i.real.segmentLottery := by
  have he : 0 < i.a + i.d - i.B ↔ 0 < i.real.a + i.real.d - i.real.B := by dsimp [real]; norm_cast
  unfold segmentLottery ThreeInput.segmentLottery
  by_cases hE : 0 < i.a + i.d - i.B
  · rw [dite_eq_left hE, dite_eq_left (he.mp hE), RationalThreeGeometryCode.compiledLottery_eq, (i.geometry hE).segmentLottery_real, i.geometry_real hE]
  · rw [dite_eq_right hE, dite_eq_right (fun h => hE (he.mpr h))]
    apply SegmentLottery.eq_of_fields
    · funext slot
      by_cases hs : slot = 0 <;> simp [RationalSegmentLottery.real, hs]
    · funext slot j
      fin_cases j <;> simp [RationalSegmentLottery.real, real]
    · funext slot j
      fin_cases j <;> simp [RationalSegmentLottery.real, real]

theorem point_fullBudget (i : RationalThreeInput) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.segmentLottery.point K slot bits j : ℝ)) := by
  apply i.segmentLottery.point_fullBudget K
  intro slot
  rw [i.segmentLottery_real]
  exact ⟨i.real.segmentLottery_endpoints.1 slot, i.real.segmentLottery_endpoints.2 slot⟩

end RationalThreeInput
end Blotto
