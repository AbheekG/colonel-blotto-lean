import Blotto.BinaryRationalOpcode

/-! Native Boolean rational registers realize the retained six-opcode
straight-line program exactly. Out-of-range reads use canonical 0/1; every
append keeps positive denominators and trims its result to semantic size.
The priced observer explicitly includes operand reads, cubic opcode work and
conservative full-prefix push copying. Counter evaluation is abstract pricing,
not a native compiler profiler. Trace-width certificates remain explicit;
whole PRG interpreter/space remains open. -/

namespace Blotto.BinaryRationalRegisterProgram
open BinaryRationalNormalization
open scoped BigOperators

def read (registers : Array SignedWord) (index : ℕ) : SignedWord := registers.getD index BinaryRationalOpcode.zero

def ValidRegisters (registers : Array SignedWord) : Prop :=
  ∀ index, BinaryRationalOpcode.Valid (read registers index)

noncomputable def interpreted (registers : Array SignedWord) : Array ℚ := registers.map value

theorem interpreted_read (registers : Array SignedWord) (index : ℕ) :
    (interpreted registers).getD index 0 = value (read registers index) := by
  by_cases h : index < registers.size
  · simp [interpreted, read, Array.getD, h]
  · simp [interpreted, read, Array.getD, h, BinaryRationalOpcode.zero_value]

def execute (instruction : RealArithmeticInstruction) (registers : Array SignedWord) : Array SignedWord :=
  registers.push (BinaryRationalOpcode.apply instruction.op
    (read registers instruction.left) (read registers instruction.right))

theorem execute_size (instruction : RealArithmeticInstruction) (registers : Array SignedWord) :
    (execute instruction registers).size = registers.size + 1 := by simp [execute]

theorem read_push_old (registers : Array SignedWord) (word : SignedWord) (index : ℕ)
    (h : index < registers.size) : read (registers.push word) index = read registers index := by
  unfold read
  simp only [Array.getD, Array.size_push]
  have hp : index < registers.size + 1 := by omega
  rw [dite_eq_left hp, dite_eq_left h]
  have hg : index < (registers.push word).size := by simp only [Array.size_push]; exact hp
  change (registers.push word)[index]'hg = registers[index]'h
  rw [Array.getElem_push, dite_eq_left h]

theorem execute_valid (instruction : RealArithmeticInstruction) (registers : Array SignedWord)
    (h : ValidRegisters registers) : ValidRegisters (execute instruction registers) := by
  intro index
  have hNew := BinaryRationalOpcode.apply_valid instruction.op
    (read registers instruction.left) (read registers instruction.right) (h instruction.left) (h instruction.right)
  by_cases hOld : index < registers.size
  · have hRead : read (execute instruction registers) index = read registers index := by
      exact read_push_old registers _ index hOld
    rw [hRead]
    exact h index
  · by_cases hAt : index = registers.size
    · subst index
      have hRead : read (execute instruction registers) registers.size =
          BinaryRationalOpcode.apply instruction.op (read registers instruction.left) (read registers instruction.right) := by
        simp [read, execute, Array.getD]
      rw [hRead]
      exact hNew
    · have hPast : ¬index < registers.size + 1 := by omega
      have hRead : read (execute instruction registers) index = BinaryRationalOpcode.zero := by
        simp [read, Array.getD, execute_size, hPast]
      rw [hRead]
      exact BinaryRationalOpcode.zero_valid

theorem execute_interpreted (instruction : RealArithmeticInstruction) (registers : Array SignedWord)
    (h : ValidRegisters registers) :
    interpreted (execute instruction registers) = instruction.executeRat (interpreted registers) := by
  unfold interpreted execute RealArithmeticInstruction.executeRat
  rw [Array.map_push, BinaryRationalOpcode.apply_value instruction.op
    (read registers instruction.left) (read registers instruction.right) (h instruction.left) (h instruction.right)]
  rw [← interpreted_read, ← interpreted_read]
  rfl

def run : List RealArithmeticInstruction → Array SignedWord → Array SignedWord
  | [], registers => registers
  | instruction :: rest, registers => run rest (execute instruction registers)

theorem run_valid (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (h : ValidRegisters registers) : ValidRegisters (run program registers) := by
  induction program generalizing registers with
  | nil => exact h
  | cons instruction rest ih => exact ih _ (execute_valid instruction registers h)

theorem run_size (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    (run program registers).size = registers.size + program.length := by
  induction program generalizing registers with
  | nil => simp [run]
  | cons instruction rest ih =>
      rw [run, ih, execute_size]
      simp only [List.length_cons]
      omega

theorem run_interpreted (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (h : ValidRegisters registers) :
    interpreted (run program registers) = RationalArithmeticProgram.run program (interpreted registers) := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (execute_valid instruction registers h), execute_interpreted instruction registers h]
      rfl

theorem run_output (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (h : ValidRegisters registers) (index : ℕ) :
    value (read (run program registers) index) =
      (RationalArithmeticProgram.run program (interpreted registers)).getD index 0 := by
  rw [← run_interpreted program registers h, interpreted_read]

def payloadWords (word : SignedWord) : ℕ := 1 + word.numerator.length + word.denominator.length

def registerPayload (registers : Array SignedWord) : ℕ := ∑ j : Fin registers.size, payloadWords (read registers j.val)

def instructionWork (instruction : RealArithmeticInstruction) (registers : Array SignedWord) : ℕ :=
  let left := read registers instruction.left
  let right := read registers instruction.right
  payloadWords left + payloadWords right +
    (BinaryRationalOpcode.applyWithWork instruction.op left right).2 +
      2 * registerPayload (execute instruction registers) + 4

def work : List RealArithmeticInstruction → Array SignedWord → ℕ
  | [], _registers => 0
  | instruction :: rest, registers => instructionWork instruction registers + work rest (execute instruction registers)

def runWithWork : List RealArithmeticInstruction → Array SignedWord → Array SignedWord × ℕ
  | [], registers => (registers, 0)
  | instruction :: rest, registers =>
      let next := execute instruction registers
      let later := runWithWork rest next
      (later.1, instructionWork instruction registers + later.2)

theorem runWithWork_refines (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    runWithWork program registers = (run program registers, work program registers) := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih => rw [runWithWork, ih]; rfl

def WordBounds (registers : Array SignedWord) (W : ℕ) : Prop := ∀ index, width (read registers index) ≤ W

theorem payloadWords_bound (word : SignedWord) (W : ℕ) (h : width word ≤ W) :
    payloadWords word ≤ 1 + 2 * W := by
  unfold payloadWords width at *
  omega

theorem registerPayload_bound (registers : Array SignedWord) (W : ℕ) (h : WordBounds registers W) :
    registerPayload registers ≤ registers.size * (1 + 2 * W) := by
  unfold registerPayload
  calc
    _ ≤ ∑ _j : Fin registers.size, (1 + 2 * W) :=
      Finset.sum_le_sum (fun j _ => payloadWords_bound _ W (h j.val))
    _ = _ := by simp

theorem instructionWork_bound (instruction : RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (hBefore : WordBounds registers W) (hAfter : WordBounds (execute instruction registers) W) :
    instructionWork instruction registers ≤
      12000 * (W + 1) ^ 3 + (2 * registers.size + 4) * (1 + 2 * W) + 4 := by
  have hL := payloadWords_bound (read registers instruction.left) W (hBefore instruction.left)
  have hR := payloadWords_bound (read registers instruction.right) W (hBefore instruction.right)
  have hCall := BinaryRationalOpcode.applyWithWork_bound instruction.op
    (read registers instruction.left) (read registers instruction.right)
  have hPair : BinaryRationalArithmetic.pairWidth (read registers instruction.left) (read registers instruction.right) ≤ W :=
    max_le (hBefore instruction.left) (hBefore instruction.right)
  have hPow := Nat.pow_le_pow_left (Nat.add_le_add_right hPair 1) 3
  have hCallBound := hCall.trans (Nat.mul_le_mul_left 12000 hPow)
  have hCopy := registerPayload_bound (execute instruction registers) W hAfter
  rw [execute_size] at hCopy
  unfold instructionWork
  dsimp only
  nlinarith

theorem run_preserves_old (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (index : ℕ) (h : index < registers.size) : read (run program registers) index = read registers index := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (by rw [execute_size]; omega)]
      exact read_push_old registers _ index h

theorem final_bounds_before (program : List RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (hZero : width BinaryRationalOpcode.zero ≤ W) (hFinal : WordBounds (run program registers) W) :
    WordBounds registers W := by
  intro index
  by_cases hi : index < registers.size
  · rw [← run_preserves_old program registers index hi]
    exact hFinal index
  · have hz : read registers index = BinaryRationalOpcode.zero := by simp [read, Array.getD, hi]
    rw [hz]
    exact hZero

def TraceWordBounds : List RealArithmeticInstruction → Array SignedWord → ℕ → Prop
  | [], registers, W => WordBounds registers W
  | instruction :: rest, registers, W =>
      WordBounds registers W ∧ TraceWordBounds rest (execute instruction registers) W

theorem final_bounds_trace (program : List RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (hZero : width BinaryRationalOpcode.zero ≤ W) (hFinal : WordBounds (run program registers) W) :
    TraceWordBounds program registers W := by
  induction program generalizing registers with
  | nil => exact hFinal
  | cons instruction rest ih =>
      exact ⟨final_bounds_before (instruction :: rest) registers W hZero hFinal,
        ih (execute instruction registers) hFinal⟩

theorem trace_bounds_final (program : List RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (h : TraceWordBounds program registers W) : WordBounds (run program registers) W := by
  induction program generalizing registers with
  | nil => exact h
  | cons instruction rest ih => exact ih _ h.2

theorem work_bound (program : List RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (hZero : width BinaryRationalOpcode.zero ≤ W) (hFinal : WordBounds (run program registers) W) :
    work program registers ≤ program.length *
      (12000 * (W + 1) ^ 3 + (2 * (registers.size + program.length) + 4) * (1 + 2 * W) + 4) := by
  induction program generalizing registers with
  | nil => simp [work]
  | cons instruction rest ih =>
      have hBefore := final_bounds_before (instruction :: rest) registers W hZero hFinal
      change WordBounds (run rest (execute instruction registers)) W at hFinal
      have hAfter := final_bounds_before rest (execute instruction registers) W hZero hFinal
      have hInstruction := instructionWork_bound instruction registers W hBefore hAfter
      have hRest := ih (execute instruction registers) hFinal
      rw [execute_size] at hRest
      simp only [work, List.length_cons]
      nlinarith

theorem work_bound_of_trace (program : List RealArithmeticInstruction) (registers : Array SignedWord) (W : ℕ)
    (hTrace : TraceWordBounds program registers W) :
    work program registers ≤ program.length *
      (12000 * (W + 1) ^ 3 + (2 * (registers.size + program.length) + 4) * (1 + 2 * W) + 4) := by
  induction program generalizing registers with
  | nil => simp [work]
  | cons instruction rest ih =>
      have hAfter : WordBounds (execute instruction registers) W := by
        cases rest with
        | nil => exact hTrace.2
        | cons next tail => exact hTrace.2.1
      have hInstruction := instructionWork_bound instruction registers W hTrace.1 hAfter
      have hRest := ih (execute instruction registers) hTrace.2
      rw [execute_size] at hRest
      simp only [work, List.length_cons]
      nlinarith

theorem runWithWork_contract (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (hValid : ValidRegisters registers) (W : ℕ) (hZero : width BinaryRationalOpcode.zero ≤ W)
    (hFinal : WordBounds (run program registers) W) :
    interpreted (runWithWork program registers).1 = RationalArithmeticProgram.run program (interpreted registers) ∧
      ValidRegisters (runWithWork program registers).1 ∧
      (runWithWork program registers).1.size = registers.size + program.length ∧
      (runWithWork program registers).2 ≤ program.length *
        (12000 * (W + 1) ^ 3 + (2 * (registers.size + program.length) + 4) * (1 + 2 * W) + 4) := by
  rw [runWithWork_refines]
  exact ⟨run_interpreted program registers hValid, run_valid program registers hValid,
    run_size program registers, work_bound program registers W hZero hFinal⟩

end Blotto.BinaryRationalRegisterProgram
