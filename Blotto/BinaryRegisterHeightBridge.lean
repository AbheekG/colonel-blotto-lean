import Blotto.BinaryRationalEncoding
import Blotto.RationalRegisterWidths

/-! Canonical parsed/encoded inputs and canonical Boolean opcode outputs
transfer retained rational final-register size certificates to actual stored
word widths. Append-only preservation supplies every intermediate trace bound;
the final work theorem has no independent Boolean-word bound hypothesis.
Source-program rational height certificates and whole PRG composition remain
explicit obligations. No quadratic/fast Rat or compiler/GC cost is inferred. -/

namespace Blotto.BinaryRegisterHeightBridge
open BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators

def CanonicalRegisters (registers : Array SignedWord) : Prop :=
  ∀ index, CanonicalWord (BinaryRationalRegisterProgram.read registers index)

theorem canonicalRegisters_valid (registers : Array SignedWord) (h : CanonicalRegisters registers) :
    BinaryRationalRegisterProgram.ValidRegisters registers := fun index => (h index).1

theorem canonicalized_registers (registers : Array SignedWord)
    (h : BinaryRationalRegisterProgram.ValidRegisters registers) : CanonicalRegisters (canonicalRegisters registers) := by
  intro index
  by_cases hi : index < registers.size
  · have hRead : BinaryRationalRegisterProgram.read (canonicalRegisters registers) index =
        BinaryRationalOpcode.canonicalize (BinaryRationalRegisterProgram.read registers index) := by
      simp [BinaryRationalRegisterProgram.read, canonicalRegisters, Array.getD, hi]
    rw [hRead]
    refine ⟨BinaryRationalOpcode.canonicalize_valid _ (h index), ?_⟩
    have hw := BinaryRationalOpcode.canonicalize_width _ (h index)
    rw [← BinaryRationalOpcode.canonicalize_value _ (h index)] at hw
    exact hw
  · have hRead : BinaryRationalRegisterProgram.read (canonicalRegisters registers) index = BinaryRationalOpcode.zero := by
      simp [BinaryRationalRegisterProgram.read, canonicalRegisters, Array.getD, hi]
    rw [hRead]
    exact zero_canonical

theorem execute_canonical (instruction : RealArithmeticInstruction) (registers : Array SignedWord)
    (h : CanonicalRegisters registers) : CanonicalRegisters (BinaryRationalRegisterProgram.execute instruction registers) := by
  intro index
  let output := BinaryRationalOpcode.apply instruction.op
    (BinaryRationalRegisterProgram.read registers instruction.left) (BinaryRationalRegisterProgram.read registers instruction.right)
  have hOut : CanonicalWord output := by
    refine ⟨BinaryRationalOpcode.apply_valid instruction.op _ _ (h instruction.left).1 (h instruction.right).1, ?_⟩
    have hw := BinaryRationalOpcode.apply_width instruction.op _ _ (h instruction.left).1 (h instruction.right).1
    rw [← BinaryRationalOpcode.apply_value instruction.op _ _ (h instruction.left).1 (h instruction.right).1] at hw
    exact hw
  by_cases hi : index < registers.size
  · rw [show BinaryRationalRegisterProgram.read (BinaryRationalRegisterProgram.execute instruction registers) index =
        BinaryRationalRegisterProgram.read registers index from
      BinaryRationalRegisterProgram.read_push_old registers output index hi]
    exact h index
  · by_cases he : index = registers.size
    · subst index
      have hRead : BinaryRationalRegisterProgram.read (BinaryRationalRegisterProgram.execute instruction registers) registers.size = output := by
        simp [BinaryRationalRegisterProgram.read, BinaryRationalRegisterProgram.execute, Array.getD, output]
      rw [hRead]
      exact hOut
    · have hp : ¬index < registers.size + 1 := by omega
      have hRead : BinaryRationalRegisterProgram.read (BinaryRationalRegisterProgram.execute instruction registers) index = BinaryRationalOpcode.zero := by
        simp [BinaryRationalRegisterProgram.read, Array.getD, BinaryRationalRegisterProgram.execute_size, hp]
      rw [hRead]
      exact zero_canonical

theorem run_canonical (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (h : CanonicalRegisters registers) : CanonicalRegisters (BinaryRationalRegisterProgram.run program registers) := by
  induction program generalizing registers with
  | nil => exact h
  | cons instruction rest ih => exact ih _ (execute_canonical instruction registers h)

theorem semantic_wordBounds (registers : Array SignedWord) (hCanonical : CanonicalRegisters registers) (W : ℕ)
    (hSemantic : RationalArithmeticProgram.WordBounds (BinaryRationalRegisterProgram.interpreted registers) W) :
    BinaryRationalRegisterProgram.WordBounds registers W := by
  intro index
  have h := (hCanonical index).2
  have hs := hSemantic index
  rw [BinaryRationalRegisterProgram.interpreted_read] at hs
  exact h.trans hs

theorem final_semantic_trace (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (hCanonical : CanonicalRegisters registers) (W : ℕ)
    (hSemantic : RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted registers)) W) :
    BinaryRationalRegisterProgram.TraceWordBounds program registers W := by
  have hValid := canonicalRegisters_valid registers hCanonical
  have hFinal := semantic_wordBounds (BinaryRationalRegisterProgram.run program registers)
    (run_canonical program registers hCanonical) W (by
      rw [BinaryRationalRegisterProgram.run_interpreted program registers hValid]
      exact hSemantic)
  have hZero : width BinaryRationalOpcode.zero ≤ W := by
    have hs := hSemantic (registers.size + program.length)
    have hSize := RationalArithmeticProgram.run_size program (BinaryRationalRegisterProgram.interpreted registers)
    have hiSize : (BinaryRationalRegisterProgram.interpreted registers).size = registers.size := by
      exact Array.size_map
    rw [hiSize] at hSize
    have hPast : ¬registers.size + program.length <
        (RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted registers)).size := by omega
    have hRead : (RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted registers)).getD
        (registers.size + program.length) 0 = 0 := by simp [Array.getD, hPast]
    rw [hRead] at hs
    exact zero_canonical.2.trans (by simpa only [BinaryRationalOpcode.zero_value] using hs)
  exact BinaryRationalRegisterProgram.final_bounds_trace program registers W hZero hFinal

theorem encoded_runWithWork_contract (program : List RealArithmeticInstruction) (input : Array SignedWord)
    (hInput : BinaryRationalRegisterProgram.ValidRegisters input) (W : ℕ)
    (hSemantic : RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted input)) W) :
    let encoded := canonicalRegisters input
    let result := BinaryRationalRegisterProgram.runWithWork program encoded
    BinaryRationalRegisterProgram.interpreted result.1 =
        RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted input) ∧
      BinaryRationalRegisterProgram.ValidRegisters result.1 ∧
      result.1.size = input.size + program.length ∧
      result.2 ≤ program.length *
        (12000 * (W + 1) ^ 3 + (2 * (input.size + program.length) + 4) * (1 + 2 * W) + 4) := by
  dsimp only
  have hCanonical := canonicalized_registers input hInput
  have hValid := canonicalRegisters_valid _ hCanonical
  have hInterpreted := BinaryRationalEncoding.canonicalRegisters_interpreted input hInput
  have hTrace := final_semantic_trace program (canonicalRegisters input) hCanonical W (by rw [hInterpreted]; exact hSemantic)
  rw [BinaryRationalRegisterProgram.runWithWork_refines]
  refine ⟨?_, BinaryRationalRegisterProgram.run_valid program _ hValid, ?_, ?_⟩
  · rw [BinaryRationalRegisterProgram.run_interpreted program _ hValid, hInterpreted]
  · simpa only [canonicalRegisters, Array.size_map] using BinaryRationalRegisterProgram.run_size program (canonicalRegisters input)
  · simpa only [canonicalRegisters, Array.size_map] using
      BinaryRationalRegisterProgram.work_bound_of_trace program (canonicalRegisters input) W hTrace

theorem encoded_final_height_trace (program : List RealArithmeticInstruction) (input : Array SignedWord)
    (hInput : BinaryRationalRegisterProgram.ValidRegisters input) (s : ℕ)
    (hHeight : ∀ index, RationalHeight
      ((RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted input)).getD index 0) s) :
    BinaryRationalRegisterProgram.TraceWordBounds program (canonicalRegisters input) (1 + 2 * s) := by
  have hSemantic : RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted input)) (1 + 2 * s) :=
    fun index => rationalWordWidth_of_height (hHeight index)
  apply final_semantic_trace program (canonicalRegisters input) (canonicalized_registers input hInput) (1 + 2 * s)
  rw [BinaryRationalEncoding.canonicalRegisters_interpreted input hInput]
  exact hSemantic

theorem encoded_final_height_work (program : List RealArithmeticInstruction) (input : Array SignedWord)
    (hInput : BinaryRationalRegisterProgram.ValidRegisters input) (s : ℕ)
    (hHeight : ∀ index, RationalHeight
      ((RationalArithmeticProgram.run program (BinaryRationalRegisterProgram.interpreted input)).getD index 0) s) :
    (BinaryRationalRegisterProgram.runWithWork program (canonicalRegisters input)).2 ≤ program.length *
      (12000 * (2 * s + 2) ^ 3 + (2 * (input.size + program.length) + 4) * (4 * s + 3) + 4) := by
  have hTrace := encoded_final_height_trace program input hInput s hHeight
  rw [BinaryRationalRegisterProgram.runWithWork_refines]
  have hWork := BinaryRationalRegisterProgram.work_bound_of_trace program (canonicalRegisters input) (1 + 2 * s) hTrace
  have hOne : 1 + 2 * s + 1 = 2 * s + 2 := by omega
  have hPayload : 1 + 2 * (1 + 2 * s) = 4 * s + 3 := by omega
  rw [hOne, hPayload] at hWork
  simpa only [canonicalRegisters, Array.size_map] using hWork

end Blotto.BinaryRegisterHeightBridge
