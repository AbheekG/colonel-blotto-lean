import Blotto.RationalThreeInput
import Blotto.ThreeDyadicCoupling

/-! Unordered rational inputs use one native coordinate swap. The resulting
descriptor equals the real three-variable descriptor exactly, for all branch
cases and all endpoint slots. -/

namespace Blotto

structure RationalThreeSpec where
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
  balance : a + d + p * c = 2 * B

namespace RationalThreeSpec

noncomputable def real (i : RationalThreeSpec) : ThreeSpec where
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
  balance := by exact_mod_cast i.balance

def orderedInput (i : RationalThreeSpec) : RationalThreeInput where
  B := i.B
  a := min i.a i.d
  d := max i.a i.d
  c := i.c
  p := i.p
  B_pos := i.B_pos
  a_pos := lt_min i.a_pos i.d_pos
  d_pos := lt_of_lt_of_le i.a_pos (le_max_left _ _)
  c_pos := i.c_pos
  p_pos := i.p_pos
  a_le := le_trans (min_le_left _ _) i.a_le
  d_le := max_le i.a_le i.d_le
  c_le := i.c_le
  p_le := i.p_le
  ordered := min_le_max
  balance := by rw [min_add_max]; exact i.balance

theorem orderedInput_real (i : RationalThreeSpec) : i.orderedInput.real = i.real.orderedInput := by
  unfold orderedInput RationalThreeInput.real real ThreeSpec.orderedInput
  simp only [Rat.cast_min, Rat.cast_max]

def segmentLottery (i : RationalThreeSpec) : RationalSegmentLottery 3 9 :=
  let l := i.orderedInput.segmentLottery
  if i.a ≤ i.d then l else
    ⟨l.weight, (fun slot => ![l.P slot 1, l.P slot 0, l.P slot 2]),
      (fun slot => ![l.Q slot 1, l.Q slot 0, l.Q slot 2]), l.nonnegative, l.mass⟩

theorem segmentLottery_real (i : RationalThreeSpec) : i.segmentLottery.real = i.real.segmentLottery := by
  have had : i.a ≤ i.d ↔ i.real.a ≤ i.real.d := by dsimp [real]; norm_cast
  have hl : i.orderedInput.segmentLottery.real = i.real.orderedInput.segmentLottery := by
    rw [i.orderedInput.segmentLottery_real, i.orderedInput_real]
  unfold segmentLottery ThreeSpec.segmentLottery
  dsimp only
  by_cases h : i.a ≤ i.d
  · rw [ite_eq_left h, ite_eq_left (had.mp h)]
    exact hl
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (had.mpr hh))]
    apply SegmentLottery.eq_of_fields
    · simpa only [RationalSegmentLottery.real, SegmentLottery.mapped] using
        congrArg (fun l : SegmentLottery 3 9 => l.weight) hl
    · have hP := congrArg SegmentLottery.P hl
      funext slot j
      fin_cases j <;> simpa [RationalSegmentLottery.real, SegmentLottery.mapped,
        AffineAllocation.swapFirst, swapFirst] using congrFun (congrFun hP slot) _
    · have hQ := congrArg SegmentLottery.Q hl
      funext slot j
      fin_cases j <;> simpa [RationalSegmentLottery.real, SegmentLottery.mapped,
        AffineAllocation.swapFirst, swapFirst] using congrFun (congrFun hQ slot) _

theorem point_fullBudget (i : RationalThreeSpec) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.segmentLottery.point K slot bits j : ℝ)) := by
  apply i.segmentLottery.point_fullBudget K
  intro slot
  rw [i.segmentLottery_real]
  exact ⟨i.real.segmentLottery_endpoints.1 slot, i.real.segmentLottery_endpoints.2 slot⟩

end RationalThreeSpec
end Blotto
