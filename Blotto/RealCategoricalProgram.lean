import Blotto.RealArithmeticProgram

/-! Categorical probability and next mass share two instructions. This fixed
scratch program allows full copying of its two small arrays; no ownership
assumption about the remaining list is used by the register allowance. -/

namespace Blotto.RealCategoricalProgram

def code : List RealArithmeticInstruction := [⟨.sub, 1, 0⟩, ⟨.div, 0, 1⟩]

noncomputable def run (weight mass : ℝ) : Array ℝ :=
  RealArithmeticProgram.run code #[weight, mass]

theorem wellFormed : RealArithmeticProgram.WellFormed 2 code := by
  norm_num [RealArithmeticProgram.WellFormed, RealArithmeticInstruction.ValidAt, code]

theorem run_eq (weight mass : ℝ) : run weight mass = #[weight, mass, mass - weight, weight / mass] := by
  simp [run, code, RealArithmeticProgram.run, RealArithmeticInstruction.execute, RealArithmeticOp.apply]

theorem run_nextMass (weight mass : ℝ) : (run weight mass).getD 2 0 = mass - weight := by
  rw [run_eq]
  simp

theorem run_probability (weight mass : ℝ) : (run weight mass).getD 3 0 = weight / mass := by
  rw [run_eq]
  simp

theorem run_size (weight mass : ℝ) : (run weight mass).size = 4 := by rw [run_eq]; rfl

theorem denominator_positive (weight mass : ℝ) (hm : 0 < mass) : 0 < (run weight mass).getD 1 0 := by
  rw [run_eq]
  simpa using hm

theorem primitiveWork : RealArithmeticProgram.primitiveWork code = 8 := rfl
theorem copyAllowance : RealArithmeticProgram.copyAllowance 2 code = 7 := rfl
theorem conservativeWork : RealArithmeticProgram.conservativeWork 2 code = 13 := rfl

-- Two external reads, two input writes, two output reads, and the mass test.
def preparationWork : ℕ := 2 + 2 + RealArithmeticProgram.conservativeWork 2 code + 2 + 1
theorem preparationWork_eq : preparationWork = 20 := rfl

def allocatedRegisterCells : ℕ := 2 + RealArithmeticProgram.copyAllowance 2 code
theorem allocatedRegisterCells_eq : allocatedRegisterCells = 9 := rfl

end Blotto.RealCategoricalProgram
