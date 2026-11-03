import Blotto.BinaryPhysicalParserTraceSparsity
import Blotto.BinaryCompleteRawCharges

/-! The actual parser event envelope closes supplied-seed raw execution's
extended ledger. These bounds retain the prior source/usage model; they do not
assert a complete native-machine price. Rejected inputs and arbitrary supplied
seed lengths are included. -/
namespace Blotto.BinaryClosedRawCharges
open BinarySeedPreparationSpace BinarySamplerExecutionCharges BinaryPRGHeapTraceUsage
set_option autoImplicit false

theorem uniform_total : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    total (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hLedger⟩ := BinaryCompleteRawCharges.uniform_parser_footprint
  obtain ⟨P,e,hParser⟩ := BinaryPhysicalParserTraceSparsity.uniform_parser_length
  refine ⟨5*P+C,max d e,?_⟩
  intro rich frame seed
  have hl := hLedger rich frame seed
  have hp := hParser frame
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  nlinarith only [hl,hp,hd,he]

theorem parsed_uniform_total : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    total (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_total
  refine ⟨C,d,?_⟩
  intro rich frame seed
  rw [BinaryCompleteRawCharges.parsed_ledger]
  exact h rich frame seed

theorem uniform_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    let produced := BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hWork⟩ := BinaryTerminalPhysicalCompleteRawMeasured.uniform_work
  obtain ⟨U,e,hUsage⟩ := BinaryTerminalPhysicalCompleteRawMeasured.uniform_usage
  obtain ⟨P,f,hLedger⟩ := uniform_total
  let D := max (max d e) f
  refine ⟨C+U+P,D,?_⟩
  intro rich frame seed
  have hw := hWork rich frame seed
  have hu := hUsage rich frame seed
  have hl := hLedger rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp [D]; omega))
  have he := Nat.mul_le_mul_left U (Nat.pow_le_pow_right hX (show e ≤ D by dsimp [D]; omega))
  have hf := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (show f ≤ D by dsimp [D]; omega))
  change (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).1.2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).1.1.1.2 ≤ _ at hw
  change usage (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).1.1.2 ≤ _ at hu
  dsimp only
  nlinarith only [hw,hu,hl,hd,he,hf]

theorem parsed_uniform_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    let produced := BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalParsedRawMeasured.uniform_joint
  obtain ⟨P,e,hLedger⟩ := parsed_uniform_total
  refine ⟨C+P,max d e,?_⟩
  intro rich frame seed
  have ho := hOld rich frame seed
  have hl := hLedger rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  change (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).1.2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).1.1.1.2+
    usage (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).1.1.2 ≤ _ at ho
  dsimp only
  nlinarith only [ho,hl,hd,he]

theorem scalar_width : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    let produced := BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed
    ∀ counter ∈ [produced.1.2,produced.2.execution.primitive,produced.2.execution.coinSource,
      produced.2.execution.write,produced.2.execution.native,produced.2.execution.wrappers,produced.2.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := uniform_joint
  refine ⟨C,d,?_⟩
  intro rich frame seed
  let produced := BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed
  have hb := hBound rich frame seed
  have hf := fields_le_total produced.2
  dsimp only [produced] at hf
  have hm := binaryWordWidth_mul C ((frame.length+1)^d)
  have hp := Farey.binaryWordWidth_power (frame.length+1) d
  have hWidth := binaryWordWidth_mono hb
  dsimp only
  intro counter hCounter
  have hc : counter ≤ produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 := by
    dsimp only [produced]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  dsimp only [produced] at hw
  omega

theorem parsed_scalar_width : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    let produced := BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed
    ∀ counter ∈ [produced.1.2,produced.2.execution.primitive,produced.2.execution.coinSource,
      produced.2.execution.write,produced.2.execution.native,produced.2.execution.wrappers,produced.2.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsed_uniform_joint
  refine ⟨C,d,?_⟩
  intro rich frame seed
  let produced := BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed
  have hb := hBound rich frame seed
  have hf := fields_le_total produced.2
  dsimp only [produced] at hf
  have hm := binaryWordWidth_mul C ((frame.length+1)^d)
  have hp := Farey.binaryWordWidth_power (frame.length+1) d
  have hWidth := binaryWordWidth_mono hb
  dsimp only
  intro counter hCounter
  have hc : counter ≤ produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 := by
    dsimp only [produced]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  dsimp only [produced] at hw
  omega

end Blotto.BinaryClosedRawCharges
