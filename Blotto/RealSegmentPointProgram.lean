import Blotto.RealArithmeticProgram
import Blotto.SegmentLottery

/-! Exact interpolation materializes one native output array. The complement
is computed once, and every coordinate uses a shared three-instruction block.
The scratch allowances permit full copies, independent of uniqueness. -/

namespace Blotto.RealSegmentPointProgram

def complementCode : List RealArithmeticInstruction := [⟨.sub, 1, 0⟩]
def coordinateCode : List RealArithmeticInstruction := [⟨.mul, 0, 1⟩, ⟨.mul, 2, 3⟩, ⟨.add, 4, 5⟩]

noncomputable def complementRun (t : ℝ) : Array ℝ :=
  RealArithmeticProgram.run complementCode #[t, 1]

noncomputable def coordinateRun (complement first t second : ℝ) : Array ℝ :=
  RealArithmeticProgram.run coordinateCode #[complement, first, t, second]

theorem complement_wellFormed : RealArithmeticProgram.WellFormed 2 complementCode := by
  norm_num [RealArithmeticProgram.WellFormed, RealArithmeticInstruction.ValidAt, complementCode]

theorem coordinate_wellFormed : RealArithmeticProgram.WellFormed 4 coordinateCode := by
  norm_num [RealArithmeticProgram.WellFormed, RealArithmeticInstruction.ValidAt, coordinateCode]

theorem complementRun_eq (t : ℝ) : complementRun t = #[t, 1, 1 - t] := by
  simp [complementRun, complementCode, RealArithmeticProgram.run,
    RealArithmeticInstruction.execute, RealArithmeticOp.apply]

theorem coordinateRun_eq (complement first t second : ℝ) :
    coordinateRun complement first t second =
      #[complement, first, t, second, complement * first, t * second, complement * first + t * second] := by
  simp [coordinateRun, coordinateCode, RealArithmeticProgram.run,
    RealArithmeticInstruction.execute, RealArithmeticOp.apply]

theorem complement_value (t : ℝ) : (complementRun t).getD 2 0 = 1 - t := by
  rw [complementRun_eq]
  simp

theorem coordinate_value (complement first t second : ℝ) :
    (coordinateRun complement first t second).getD 6 0 = complement * first + t * second := by
  rw [coordinateRun_eq]
  simp

noncomputable def output {n : ℕ} (P Q : Allocation n) (t : ℝ) : FixedArrayTable n ℝ :=
  let complement := (complementRun t).getD 2 0
  FixedArrayTable.ofFn fun j => (coordinateRun complement (P j) t (Q j)).getD 6 0

theorem output_refines {n : ℕ} (P Q : Allocation n) (t : ℝ) :
    (output P Q t).read = segmentPoint P Q t := by
  funext j
  simp only [output, FixedArrayTable.read_ofFn, coordinate_value, complement_value]
  rfl

theorem output_fullBudget {n : ℕ} (P Q : Allocation n) {B t : ℝ}
    (hP : FullBudget B P) (hQ : FullBudget B Q) (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget B (output P Q t).read := by
  rw [output_refines]
  exact segment_fullBudget hP hQ ht

theorem output_inBox {n : ℕ} (P Q length : Allocation n) {t : ℝ}
    (hP : InBox length P) (hQ : InBox length Q) (ht : 0 ≤ t ∧ t ≤ 1) :
    InBox length (output P Q t).read := by
  rw [output_refines]
  exact segment_inBox hP hQ ht

-- Reads/initial writes/output read price the fixed scratch programs.
def complementWork : ℕ := 2 + 2 + RealArithmeticProgram.conservativeWork 2 complementCode + 1
def coordinateWork : ℕ := 4 + 4 + RealArithmeticProgram.conservativeWork 4 coordinateCode + 1

theorem complementWork_eq : complementWork = 11 := rfl
theorem coordinateWork_eq : coordinateWork = 36 := rfl

-- One final output-array write per coordinate, besides the register block.
def outputWork (n : ℕ) : ℕ := complementWork + n * (coordinateWork + 1)
theorem outputWork_eq (n : ℕ) : outputWork n = 37 * n + 11 := by
  simp only [outputWork, complementWork_eq, coordinateWork_eq]
  omega

def registerCells (n : ℕ) : ℕ :=
  (2 + RealArithmeticProgram.copyAllowance 2 complementCode) +
    n * (4 + RealArithmeticProgram.copyAllowance 4 coordinateCode)

theorem registerCells_eq (n : ℕ) : registerCells n = 22 * n + 5 := by
  simp only [registerCells, RealArithmeticProgram.copyAllowance, complementCode, coordinateCode]
  omega

end Blotto.RealSegmentPointProgram
