import Blotto.BinaryRationalOpcodeAllocation
import Blotto.BinaryRationalRegisterStorage

/-! Opcode buffers compose with the actual append-only register runner.
The observer conservatively retains every opcode's structurally proved workspace
until return, in addition to prefix arrays and push/control storage. The complete
PRG controller/input parser and native allocator/GC remain separate. -/

namespace Blotto.BinaryRationalRegisterProgram
open BinaryRationalNormalization

def opcodeWorkspace (instruction : RealArithmeticInstruction) (registers : Array SignedWord) : ℕ :=
  BinaryRationalOpcodeAllocation.opcodeStorage instruction.op
    (read registers instruction.left) (read registers instruction.right)

def retainedOpcodeWorkspace : List RealArithmeticInstruction → Array SignedWord → ℕ
  | [], _ => 0
  | instruction :: rest, registers =>
      opcodeWorkspace instruction registers + retainedOpcodeWorkspace rest (execute instruction registers)

def storageWithWorkspace (program : List RealArithmeticInstruction) (registers : Array SignedWord) : ℕ :=
  pushStorageAllowance program registers + retainedOpcodeWorkspace program registers

def runWithWorkspace : List RealArithmeticInstruction → Array SignedWord → Array SignedWord × ℕ
  | [], registers => (registers, 0)
  | instruction :: rest, registers =>
      let evaluated := BinaryRationalOpcodeAllocation.applyWithAllocation instruction.op
        (read registers instruction.left) (read registers instruction.right)
      let later := runWithWorkspace rest (registers.push evaluated.1)
      (later.1, opcodeWorkspace instruction registers + later.2)

theorem runWithWorkspace_state (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    runWithWorkspace program registers = (run program registers, retainedOpcodeWorkspace program registers) := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [runWithWorkspace, BinaryRationalOpcodeAllocation.applyWithAllocation_state, run,
      execute, retainedOpcodeWorkspace, ih]

theorem opcodeWorkspace_bound (instruction : RealArithmeticInstruction) (registers : Array SignedWord)
    (W : ℕ) (h : WordBounds registers W) : opcodeWorkspace instruction registers ≤ 2000000 * (W + 2) ^ 4 := by
  have he := BinaryRationalOpcodeAllocation.opcodeStorage_bound instruction.op
    (read registers instruction.left) (read registers instruction.right)
  have hPair : BinaryRationalArithmetic.pairWidth (read registers instruction.left) (read registers instruction.right) ≤ W :=
    max_le (h instruction.left) (h instruction.right)
  exact he.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hPair 2) 4))

theorem retainedOpcodeWorkspace_bound (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (W : ℕ) (h : TraceWordBounds program registers W) :
    retainedOpcodeWorkspace program registers ≤ program.length * (2000000 * (W + 2) ^ 4) := by
  induction program generalizing registers with
  | nil => simp [retainedOpcodeWorkspace]
  | cons instruction rest ih =>
    have hHead := opcodeWorkspace_bound instruction registers W h.1
    have hRest := ih (execute instruction registers) h.2
    simp only [retainedOpcodeWorkspace, List.length_cons]
    nlinarith

theorem storageWithWorkspace_bound (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (W : ℕ) (h : TraceWordBounds program registers W) :
    storageWithWorkspace program registers ≤
      (program.length + 3) * (registers.size + program.length) * (1 + 2 * W) +
        4 * (program.length + 1) + program.length * (2000000 * (W + 2) ^ 4) := by
  exact Nat.add_le_add (pushStorageAllowance_bound program registers W h)
    (retainedOpcodeWorkspace_bound program registers W h)

theorem canonical_semantic_workspace (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (hCanonical : BinaryRegisterHeightBridge.CanonicalRegisters registers) (W : ℕ)
    (hSemantic : RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run program (interpreted registers)) W) :
    storageWithWorkspace program registers ≤
      (program.length + 3) * (registers.size + program.length) * (1 + 2 * W) +
        4 * (program.length + 1) + program.length * (2000000 * (W + 2) ^ 4) :=
  storageWithWorkspace_bound program registers W
    (BinaryRegisterHeightBridge.final_semantic_trace program registers hCanonical W hSemantic)

end Blotto.BinaryRationalRegisterProgram

namespace Blotto.BinaryRationalPairProgram.Source

theorem pair_storage_with_opcode_workspace (source : Source) {s : ℕ}
    (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    BinaryRationalRegisterProgram.storageWithWorkspace RealPairProgram.code source.inputs ≤
      120 * (64 * s + 63) + 32 + 7 * (2000000 * (32 * s + 33) ^ 4) := by
  have he := BinaryRationalRegisterProgram.storageWithWorkspace_bound RealPairProgram.code source.inputs
    (32 * s + 31) (source.trace_wordBounds h hs)
  have hSize : source.inputs.size = 5 := rfl
  rw [hSize, RealPairProgram.operations] at he
  convert he using 1
  ring

theorem pair_workspace_lattice (source : Source) {D : ℕ} (hD : 0 < D)
    (h : source.pair.Lattice D) (hi : source.pair.lengthI ≤ 1) (hj : source.pair.lengthJ ≤ 1) :
    BinaryRationalRegisterProgram.storageWithWorkspace RealPairProgram.code source.inputs ≤
      120 * (64 * binaryWordWidth D + 191) + 32 +
        7 * (2000000 * (32 * binaryWordWidth D + 97) ^ 4) := by
  have he := source.pair_storage_with_opcode_workspace
    (RationalPairProgram.fieldsHeight_lattice source.pair hD h hi hj) (by omega)
  have hPayload : 64 * (2 + binaryWordWidth D) + 63 = 64 * binaryWordWidth D + 191 := by omega
  have hScratch : 32 * (2 + binaryWordWidth D) + 33 = 32 * binaryWordWidth D + 97 := by omega
  rw [hPayload, hScratch] at he
  exact he

theorem pair_binary_execution_contract (source : Source) {s : ℕ}
    (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    (BinaryRationalRegisterProgram.runWithWorkspace RealPairProgram.code source.inputs).1 = source.run ∧
      BinaryRegisterHeightBridge.CanonicalRegisters source.run ∧
      source.run.size = 12 ∧
      BinaryRationalNormalization.value (BinaryRationalRegisterProgram.read source.run 7) = source.pair.lower ∧
      BinaryRationalNormalization.value (BinaryRationalRegisterProgram.read source.run 8) = source.pair.upper ∧
      BinaryRationalNormalization.value (BinaryRationalRegisterProgram.read source.run 11) = source.pair.probability ∧
      source.runWithWork.2 ≤ 7 * (12000 * (32 * s + 32) ^ 3 + 28 * (64 * s + 63) + 4) ∧
      BinaryRationalRegisterProgram.storageWithWorkspace RealPairProgram.code source.inputs ≤
        120 * (64 * s + 63) + 32 + 7 * (2000000 * (32 * s + 33) ^ 4) := by
  rw [BinaryRationalRegisterProgram.runWithWorkspace_state]
  exact ⟨rfl, source.run_canonical, source.run_size, source.run_lower, source.run_upper,
    source.run_probability, source.work_bound h hs, source.pair_storage_with_opcode_workspace h hs⟩

end Blotto.BinaryRationalPairProgram.Source
