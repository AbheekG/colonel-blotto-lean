import Blotto.FixedArrayTable
import Blotto.Rounding

/-! A straight-line real-arithmetic primitive model with shared registers.
Each instruction reads two registers, performs one named real operation and
appends one result. Physical register allocation/ownership is separate. -/

namespace Blotto

inductive RealArithmeticOp where
  | add | sub | mul | div | minimum | maximum

namespace RealArithmeticOp

noncomputable def apply : RealArithmeticOp → ℝ → ℝ → ℝ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .minimum, x, y => min x y
  | .maximum, x, y => max x y

end RealArithmeticOp

structure RealArithmeticInstruction where
  op : RealArithmeticOp
  left : ℕ
  right : ℕ

namespace RealArithmeticInstruction

noncomputable def execute (i : RealArithmeticInstruction) (registers : Array ℝ) : Array ℝ :=
  registers.push (i.op.apply (registers.getD i.left 0) (registers.getD i.right 0))

def ValidAt (i : RealArithmeticInstruction) (size : ℕ) : Prop := i.left < size ∧ i.right < size

theorem execute_size (i : RealArithmeticInstruction) (registers : Array ℝ) :
    (i.execute registers).size = registers.size + 1 := by simp [execute]

end RealArithmeticInstruction

namespace RealArithmeticProgram

noncomputable def run : List RealArithmeticInstruction → Array ℝ → Array ℝ
  | [], registers => registers
  | instruction :: rest, registers => run rest (instruction.execute registers)

def WellFormed : ℕ → List RealArithmeticInstruction → Prop
  | _, [] => True
  | size, instruction :: rest => instruction.ValidAt size ∧ WellFormed (size + 1) rest

def primitiveWork (program : List RealArithmeticInstruction) : ℕ := 4 * program.length

def copyAllowance : ℕ → List RealArithmeticInstruction → ℕ
  | _, [] => 0
  | size, _ :: rest => size + 1 + copyAllowance (size + 1) rest

def conservativeWork (size : ℕ) (program : List RealArithmeticInstruction) : ℕ :=
  3 * program.length + copyAllowance size program

theorem copyAllowance_bound (size : ℕ) (program : List RealArithmeticInstruction) :
    copyAllowance size program ≤ program.length * (size + program.length) := by
  induction program generalizing size with
  | nil => simp [copyAllowance]
  | cons instruction rest ih =>
    have h := ih (size + 1)
    simp only [copyAllowance, List.length_cons]
    nlinarith

theorem run_size (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    (run program registers).size = registers.size + program.length := by
  induction program generalizing registers with
  | nil => simp [run]
  | cons instruction rest ih =>
    rw [run, ih, instruction.execute_size]
    simp only [List.length_cons]
    omega

theorem run_append (first second : List RealArithmeticInstruction) (registers : Array ℝ) :
    run (first ++ second) registers = run second (run first registers) := by
  induction first generalizing registers with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.execute registers)

end RealArithmeticProgram
end Blotto
