import Blotto.WordMachineMap
import Blotto.RationalSegmentProgram

/-! Native categorical control followed by rational segment emission at a
supplied scalar block. This controller is suitable for serial composition:
it makes no nested sampling call and inherits one cap from its caller. -/

namespace Blotto.RationalSegmentLottery

def machine {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ)
    (scalarBits : Fin K → Bool) : WordStateMachine (CategoricalState (Fin k)) (Fin n → ℚ) :=
  (categoricalMachine fallback).mapped (fun slot => l.point K slot scalarBits)

theorem machine_rank {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ)
    (scalarBits : Fin K → Bool) : (l.machine fallback K scalarBits).rank l.start = k - 1 := by
  simp [machine, WordStateMachine.mapped, categoricalMachine, categoricalRank, start, rationalWeightList]

theorem machine_mean {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ)
    (scalarBits : Fin K → Bool) (f : (Fin n → ℚ) → ℝ) :
    ((l.machine fallback K scalarBits).specification l.start).decode.mean f =
      ∑ slot, (l.weight slot : ℝ) * f (l.point K slot scalarBits) := by
  rw [machine, WordStateMachine.mapped_mean]
  exact rationalCategorical_mean l.weight l.nonnegative l.mass fallback _

theorem machine_forLeaves {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ)
    (scalarBits : Fin K → Bool) (P : (Fin n → ℚ) → Prop) (hP : ∀ slot, P (l.point K slot scalarBits)) :
    ((l.machine fallback K scalarBits).specification l.start).decode.ForLeaves P := by
  apply (l.machine fallback K scalarBits).specification_forLeaves (fun _ => True) P _ l.start trivial
  intro cursor _
  unfold machine WordStateMachine.mapped
  dsimp only
  cases hs : (categoricalMachine fallback).step cursor with
  | done slot => exact hP slot
  | ask a b hb hab upper lower => exact ⟨trivial, trivial⟩

end Blotto.RationalSegmentLottery
