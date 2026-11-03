import Blotto.RealSegmentFlat
import Blotto.RealCategoricalWork

/-! The actual segment draw's shared-register and uniform-choice stages.
Descriptor formula evaluation, weight-list initialization, generic controller
bookkeeping and physical allocation remain separate from this component. -/

namespace Blotto.SegmentLottery

noncomputable def realArithmeticAndChoiceWork {n k : ℕ} (l : SegmentLottery n k)
    (fallback : Fin k) (seed : Fin ((k - 1) + 1) → ℝ) : ℕ :=
  realCategoricalArithmeticAndChoiceWork l.weight l.nonnegative fallback (Fin.tail seed) +
    RealSegmentPointProgram.outputWork n + 1

theorem realArithmeticAndChoiceWork_bound {n k : ℕ} (l : SegmentLottery n k)
    (fallback : Fin k) (seed : Fin ((k - 1) + 1) → ℝ) :
    l.realArithmeticAndChoiceWork fallback seed ≤ 22 * k + 37 * n + 12 := by
  have hc := realCategoricalArithmeticAndChoiceWork_bound l.weight l.nonnegative fallback (Fin.tail seed)
  unfold realArithmeticAndChoiceWork
  rw [RealSegmentPointProgram.outputWork_eq]
  omega

noncomputable def realRegisterCellsAllowance {n k : ℕ} (l : SegmentLottery n k)
    (fallback : Fin k) (seed : Fin ((k - 1) + 1) → ℝ) : ℕ :=
  (realCategoricalMachine fallback).callbackWork realCategoricalRegisterCellsCharge (k - 1)
    (Fin.tail seed) (.remaining (realWeightTable l.weight l.nonnegative)) 0 (Nat.zero_le _) +
      RealSegmentPointProgram.registerCells n

theorem realRegisterCellsAllowance_bound {n k : ℕ} (l : SegmentLottery n k)
    (fallback : Fin k) (seed : Fin ((k - 1) + 1) → ℝ) :
    l.realRegisterCellsAllowance fallback seed ≤ 9 * k + 22 * n + 5 := by
  have hc := realCategoricalRegisterCells_bound l.weight l.nonnegative fallback (Fin.tail seed)
  unfold realRegisterCellsAllowance
  rw [RealSegmentPointProgram.registerCells_eq]
  omega

theorem realThreeArithmeticAndChoiceWork_bound (l : SegmentLottery 3 9) (seed : Fin 9 → ℝ) :
    l.realArithmeticAndChoiceWork 0 seed ≤ 321 :=
  l.realArithmeticAndChoiceWork_bound 0 seed

theorem realResidualArithmeticAndChoiceWork_bound (l : SegmentLottery 3 3) (seed : Fin 3 → ℝ) :
    l.realArithmeticAndChoiceWork 0 seed ≤ 189 :=
  l.realArithmeticAndChoiceWork_bound 0 seed

theorem realFourGluingArithmeticAndChoiceWork_bound (l : SegmentLottery 4 81) (seed : Fin 81 → ℝ) :
    l.realArithmeticAndChoiceWork 0 seed ≤ 1942 :=
  l.realArithmeticAndChoiceWork_bound 0 seed

end Blotto.SegmentLottery
