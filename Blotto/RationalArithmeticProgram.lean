import Blotto.RealArithmeticProgram

/-! Native rational evaluation of the shared-register instruction set.
Arithmetic-call counts use the same code; bit costs require operand sizes
and explicit integer-backend contracts in addition to those counts. -/

namespace Blotto.RealArithmeticOp

def applyRat : RealArithmeticOp → ℚ → ℚ → ℚ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .minimum, x, y => min x y
  | .maximum, x, y => max x y

theorem applyRat_real (op : RealArithmeticOp) (x y : ℚ) : (op.applyRat x y : ℝ) = op.apply x y := by
  cases op <;> simp [applyRat, apply]

end Blotto.RealArithmeticOp
namespace Blotto.RealArithmeticInstruction

def executeRat (i : RealArithmeticInstruction) (registers : Array ℚ) : Array ℚ :=
  registers.push (i.op.applyRat (registers.getD i.left 0) (registers.getD i.right 0))

theorem executeRat_size (i : RealArithmeticInstruction) (registers : Array ℚ) :
    (i.executeRat registers).size = registers.size + 1 := by simp [executeRat]

end Blotto.RealArithmeticInstruction
namespace Blotto.RationalArithmeticProgram

def run : List RealArithmeticInstruction → Array ℚ → Array ℚ
  | [], registers => registers
  | instruction :: rest, registers => run rest (instruction.executeRat registers)

theorem run_size (program : List RealArithmeticInstruction) (registers : Array ℚ) :
    (run program registers).size = registers.size + program.length := by
  induction program generalizing registers with
  | nil => simp [run]
  | cons instruction rest ih =>
    rw [run, ih, instruction.executeRat_size]
    simp only [List.length_cons]
    omega

theorem run_append (first second : List RealArithmeticInstruction) (registers : Array ℚ) :
    run (first ++ second) registers = run second (run first registers) := by
  induction first generalizing registers with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.executeRat registers)

end Blotto.RationalArithmeticProgram
