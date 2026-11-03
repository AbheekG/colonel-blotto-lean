import Blotto.BinaryRationalPairProgram

/-! Stored-register payload throughout the actual append-only Boolean program.
The conservative observer accounts for both arrays during a push and all retained
prefix frames. Opcode internal workspace, allocator headers and GC are separate;
no physical-heap claim is inferred from register payload. -/

namespace Blotto.BinaryRationalRegisterProgram
open BinaryRationalNormalization

theorem run_append (first second : List RealArithmeticInstruction) (registers : Array SignedWord) :
    run (first ++ second) registers = run second (run first registers) := by
  induction first generalizing registers with
  | nil => rfl
  | cons instruction rest ih => exact ih (execute instruction registers)

theorem trace_prefix (first second : List RealArithmeticInstruction) (registers : Array SignedWord)
    (W : ℕ) (h : TraceWordBounds (first ++ second) registers W) :
    WordBounds (run first registers) W := by
  induction first generalizing registers with
  | nil =>
    cases second with
    | nil => exact h
    | cons instruction rest => exact h.1
  | cons instruction rest ih => exact ih (execute instruction registers) h.2

theorem prefix_registerPayload_bound (first second : List RealArithmeticInstruction)
    (registers : Array SignedWord) (W : ℕ) (h : TraceWordBounds (first ++ second) registers W) :
    registerPayload (run first registers) ≤
      (registers.size + (first ++ second).length) * (1 + 2 * W) := by
  have hp := registerPayload_bound (run first registers) W (trace_prefix first second registers W h)
  rw [run_size] at hp
  exact hp.trans (Nat.mul_le_mul_right _ (by simp only [List.length_append]; omega))

def registerPushPayload (instruction : RealArithmeticInstruction) (registers : Array SignedWord) : ℕ :=
  registerPayload registers + registerPayload (execute instruction registers)

def peakRegisterPayload : List RealArithmeticInstruction → Array SignedWord → ℕ
  | [], registers => registerPayload registers
  | instruction :: rest, registers =>
      max (registerPushPayload instruction registers)
        (peakRegisterPayload rest (execute instruction registers))

theorem peakRegisterPayload_bound (program : List RealArithmeticInstruction)
    (registers : Array SignedWord) (W : ℕ) (h : TraceWordBounds program registers W) :
    peakRegisterPayload program registers ≤
      2 * (registers.size + program.length) * (1 + 2 * W) := by
  induction program generalizing registers with
  | nil =>
    simp only [peakRegisterPayload, List.length_nil, Nat.add_zero]
    have hb := registerPayload_bound registers W h
    nlinarith
  | cons instruction rest ih =>
    have hAfter : WordBounds (execute instruction registers) W := by
      cases rest with
      | nil => exact h.2
      | cons next tail => exact h.2.1
    have hBefore := registerPayload_bound registers W h.1
    have hNext := registerPayload_bound (execute instruction registers) W hAfter
    have hRest := ih (execute instruction registers) h.2
    rw [execute_size] at hNext hRest
    simp only [peakRegisterPayload, List.length_cons, registerPushPayload]
    apply max_le
    · nlinarith
    · nlinarith

def retainedRegisterPayload : List RealArithmeticInstruction → Array SignedWord → ℕ
  | [], registers => registerPayload registers
  | instruction :: rest, registers =>
      registerPayload registers + retainedRegisterPayload rest (execute instruction registers)

theorem retainedRegisterPayload_bound (program : List RealArithmeticInstruction)
    (registers : Array SignedWord) (W : ℕ) (h : TraceWordBounds program registers W) :
    retainedRegisterPayload program registers ≤
      (program.length + 1) * (registers.size + program.length) * (1 + 2 * W) := by
  induction program generalizing registers with
  | nil => simpa only [retainedRegisterPayload, List.length_nil, Nat.add_zero, Nat.zero_add, Nat.one_mul]
      using registerPayload_bound registers W h
  | cons instruction rest ih =>
    have hBefore := registerPayload_bound registers W h.1
    have hRest := ih (execute instruction registers) h.2
    rw [execute_size] at hRest
    simp only [retainedRegisterPayload, List.length_cons]
    nlinarith

def pushStorageAllowance (program : List RealArithmeticInstruction) (registers : Array SignedWord) : ℕ :=
  retainedRegisterPayload program registers + peakRegisterPayload program registers + 4 * (program.length + 1)

theorem pushStorageAllowance_bound (program : List RealArithmeticInstruction)
    (registers : Array SignedWord) (W : ℕ) (h : TraceWordBounds program registers W) :
    pushStorageAllowance program registers ≤
      (program.length + 3) * (registers.size + program.length) * (1 + 2 * W) + 4 * (program.length + 1) := by
  have hr := retainedRegisterPayload_bound program registers W h
  have hp := peakRegisterPayload_bound program registers W h
  unfold pushStorageAllowance
  nlinarith

theorem canonical_semantic_storage_bound (program : List RealArithmeticInstruction)
    (registers : Array SignedWord) (hCanonical : BinaryRegisterHeightBridge.CanonicalRegisters registers)
    (W : ℕ) (hSemantic : RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run program (interpreted registers)) W) :
    pushStorageAllowance program registers ≤
      (program.length + 3) * (registers.size + program.length) * (1 + 2 * W) + 4 * (program.length + 1) :=
  pushStorageAllowance_bound program registers W
    (BinaryRegisterHeightBridge.final_semantic_trace program registers hCanonical W hSemantic)

end Blotto.BinaryRationalRegisterProgram

namespace Blotto.BinaryRationalPairProgram.Source

theorem pair_peak_registerPayload (source : Source) {s : ℕ}
    (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    BinaryRationalRegisterProgram.peakRegisterPayload RealPairProgram.code source.inputs ≤
      24 * (64 * s + 63) := by
  have hp := BinaryRationalRegisterProgram.peakRegisterPayload_bound RealPairProgram.code source.inputs
    (32 * s + 31) (source.trace_wordBounds h hs)
  have hSize : source.inputs.size = 5 := rfl
  rw [hSize, RealPairProgram.operations] at hp
  convert hp using 1
  ring

theorem pair_pushStorageAllowance (source : Source) {s : ℕ}
    (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    BinaryRationalRegisterProgram.pushStorageAllowance RealPairProgram.code source.inputs ≤
      120 * (64 * s + 63) + 32 := by
  have hp := BinaryRationalRegisterProgram.pushStorageAllowance_bound RealPairProgram.code source.inputs
    (32 * s + 31) (source.trace_wordBounds h hs)
  have hSize : source.inputs.size = 5 := rfl
  rw [hSize, RealPairProgram.operations] at hp
  convert hp using 1
  ring

end Blotto.BinaryRationalPairProgram.Source
