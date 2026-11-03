import Blotto.RationalAllocationProgram
import Blotto.RationalUniformGroupLottery
import Blotto.RationalFourSpecMachine

/-! Native grouped-coordinate continuations: rank eight for the uniform
case, and at most eighty when a fractional coordinate is retained. -/

namespace Blotto

namespace RationalUniformGroupSpec

def program {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (scalarBits : Fin K → Bool) : RationalAllocationProgram m 8 where
  State := CategoricalState (Fin 9)
  machine := (i.lottery hm).machine 0 K scalarBits
  start := (i.lottery hm).start
  rank_le := by rw [RationalSegmentLottery.machine_rank]

theorem program_leavesBudget {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (scalarBits : Fin K → Bool) : (i.program hm K scalarBits).LeavesBudget i.B :=
  (i.lottery hm).machine_forLeaves 0 K scalarBits _ (fun slot => i.lottery_point_fullBudget hm K slot scalarBits)

end RationalUniformGroupSpec

namespace RationalMixedGroupSpec

def program {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : RationalAllocationProgram (m + 1) 80 := by
  by_cases h2 : m = 2
  · subst m
    exact ⟨CategoricalState (Fin 9), i.threeInput.segmentLottery.machine 0 K scalarBits,
      i.threeInput.segmentLottery.start, by rw [RationalSegmentLottery.machine_rank]; decide⟩
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact ⟨FourSamplingState i.fourInput.input, i.fourInput.machine K outerBits scalarBits,
      i.fourInput.input.start K outerBits scalarBits, i.fourInput.machine_rank K outerBits scalarBits⟩

theorem program_leavesBudget {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) : (i.program hm K outerBits scalarBits).LeavesBudget i.B := by
  rcases hm with rfl | rfl
  · exact i.threeInput.segmentLottery.machine_forLeaves 0 K scalarBits _
      (fun slot => i.threeInput.point_fullBudget K slot scalarBits)
  · exact i.fourInput.machine_forLeaves K outerBits scalarBits

end RationalMixedGroupSpec
end Blotto
