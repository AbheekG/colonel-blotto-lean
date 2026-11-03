import Blotto.RealArithmeticProgram

/-! Pair endpoints and probability use a shared seven-instruction program.
Inputs are the two caps, two resources and a zero register. Every operand is
available before use, and the exact values are the retained rounding formulas. -/

namespace Blotto.RealPairProgram

def code : List RealArithmeticInstruction :=
  [⟨.add, 2, 3⟩, ⟨.sub, 5, 1⟩, ⟨.maximum, 4, 6⟩,
    ⟨.minimum, 0, 5⟩, ⟨.sub, 2, 7⟩, ⟨.sub, 8, 7⟩, ⟨.div, 9, 10⟩]

noncomputable def inputs (p : RoundingPair) : Array ℝ :=
  #[p.lengthI, p.lengthJ, p.resourceI, p.resourceJ, 0]

noncomputable def run (p : RoundingPair) : Array ℝ := RealArithmeticProgram.run code (inputs p)

theorem wellFormed : RealArithmeticProgram.WellFormed 5 code := by
  norm_num [RealArithmeticProgram.WellFormed, RealArithmeticInstruction.ValidAt, code]

theorem operations : code.length = 7 := rfl
theorem primitiveWork : RealArithmeticProgram.primitiveWork code = 28 := rfl
theorem copyAllowance : RealArithmeticProgram.copyAllowance 5 code = 63 := rfl
theorem conservativeWork : RealArithmeticProgram.conservativeWork 5 code = 84 := rfl

def preparationWork : ℕ := 4 + 5 + RealArithmeticProgram.conservativeWork 5 code + 3
theorem preparationWork_eq : preparationWork = 96 := rfl

theorem run_eq (p : RoundingPair) : run p =
    #[p.lengthI, p.lengthJ, p.resourceI, p.resourceJ, 0, p.total, p.total - p.lengthJ,
      p.lower, p.upper, p.resourceI - p.lower, p.upper - p.lower, p.probability] := by
  simp [run, code, inputs, RealArithmeticProgram.run, RealArithmeticInstruction.execute,
    RealArithmeticOp.apply, RoundingPair.total, RoundingPair.lower, RoundingPair.upper, RoundingPair.probability]

theorem run_lower (p : RoundingPair) : (run p).getD 7 0 = p.lower := by rw [run_eq]; simp
theorem run_upper (p : RoundingPair) : (run p).getD 8 0 = p.upper := by rw [run_eq]; simp
theorem run_probability (p : RoundingPair) : (run p).getD 11 0 = p.probability := by rw [run_eq]; simp

theorem denominator_positive (p : RoundingPair) : 0 < (run p).getD 10 0 := by
  rw [run_eq]
  simpa using sub_pos.mpr p.lower_lt_upper

def allocatedRegisterCells : ℕ := 5 + RealArithmeticProgram.copyAllowance 5 code
theorem allocatedRegisterCells_eq : allocatedRegisterCells = 68 := rfl

theorem run_size (p : RoundingPair) : (run p).size = 12 := by rw [run_eq]; rfl

end Blotto.RealPairProgram
