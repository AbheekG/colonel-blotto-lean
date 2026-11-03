import Blotto.BinaryCompleteFramedCharges
import Blotto.BinarySeedValidationTraceBounds

/-! The actual complete seed runner has a frame-only extended ledger bound,
uniformly over all supplied seeds. Accepted store parameters remove the old
numerical-cap access parameter at this seed-prepared interface. -/
namespace Blotto.BinaryCompleteSeedCharges
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinarySamplerExecutionCharges
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryTerminalPhysicalCompleteSeedMeasured
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem framed_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1 parsed.1.2.logical.request.precision),
    let drawn := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed
      (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich parsed.1.2.logical.request.precision
      blocks.outer blocks.scalar parsed.1.2.logical.header
    drawn.1.2+BinaryBigEndian.littleValue drawn.1.1.1.2+usage drawn.1.1.2+
      BinaryExecutionCharges.total drawn.2+drawn.1.1.2.length ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hFull⟩ := BinaryCompleteFramedCharges.accepted_uniform_joint
  obtain ⟨T,e,hTrace⟩ := BinaryCompleteFramedCharges.accepted_framed_trace_footprint
  let D := max d e
  refine ⟨(30*C+T)*20000^D,D,?_⟩
  intro frame parsed hParsed rich blocks
  let store := (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1
  let drawn := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed store rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  let Q := frame.length+parsed.1.2.logical.request.precision+store.width+store.cap.value+parsed.1.2.logical.header.bytes.length+3
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hL : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have hf := hFull frame parsed hParsed store rich parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  have ht := hTrace frame parsed hParsed store rich parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  change drawn.1.2+BinaryBigEndian.littleValue drawn.1.1.1.2+usage drawn.1.1.2+BinaryExecutionCharges.total drawn.2 ≤ C*Q^d at hf
  change drawn.1.1.2.length ≤ 26*drawn.1.2+3*usage drawn.1.1.2+T*(frame.length+3)^e at ht
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hQ (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left T ((Nat.pow_le_pow_left hL e).trans (Nat.pow_le_pow_right hQ (Nat.le_max_right d e)))
  have hs := store_parameters frame parsed hParsed blocks
  change Q ≤ 20000*(frame.length+1) at hs
  have hp := Nat.mul_le_mul_left (30*C+T) (Nat.pow_le_pow_left hs D)
  rw [Nat.mul_pow] at hp
  change drawn.1.2+BinaryBigEndian.littleValue drawn.1.1.1.2+usage drawn.1.1.2+
    BinaryExecutionCharges.total drawn.2+drawn.1.1.2.length ≤ ((30*C+T)*20000^D)*(frame.length+1)^D
  dsimp only [D] at *
  nlinarith only [hf,ht,hd,he,hp]

theorem accepted_uniform_charges : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    total (runWithCharges frame parsed hParsed rich seed).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hFramed⟩ := framed_joint
  let D := max d 1
  refine ⟨6*C+8000000,D,?_⟩
  intro frame parsed hParsed rich seed
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  let X := frame.length+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hPW := BinaryTerminalPhysicalPreparationWork.preparation_frame_bound frame parsed hParsed seed
  have hPT := BinarySeedValidationTraceBounds.preparation_length parsed.1.2.logical seed
  have hPE := BinarySeedPreparationEmission.prepare_emission parsed.1.2.logical seed
  rw [BinarySeedPreparationEmission.prepare_compat] at hPE
  change prepared.2 ≤ 128000*X at hPW
  change prepared.1.2.length ≤ prepared.2+5 at hPT
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : X ≤ X^D := by simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ (by omega)
  unfold runWithCharges
  dsimp only
  simp only [BinarySeedPreparationEmission.prepare_compat]
  split
  · simp only [total_addWrapper,total_ofExecution,BinarySamplerExecutionCharges.zero,BinaryExecutionCharges.total,
      BinaryWrapperEmission.one_work]
    dsimp only [prepared] at hPW hPT
    dsimp only [X,D] at *
    nlinarith only [hPW,hPT,hPE,hLinear,hOne]
  · rename_i held hPrepared
    obtain ⟨blocks,hHeld⟩ := prepared_some parsed.1.2.logical seed held hPrepared
    subst held
    have hf := hFramed frame parsed hParsed rich blocks
    have hs := BinarySeedValidationTraceBounds.store_length frame parsed hParsed blocks
    simp only [total_addWrapper,total_ofExecution,BinarySeedWrapperEmission.nested_work]
    dsimp only [prepared] at hPW hPT
    dsimp only [X,D] at *
    nlinarith only [hf,hs,hPW,hPT,hPE,hd,hLinear,hOne]

theorem accepted_uniform_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    let produced := runWithCharges frame parsed hParsed rich seed
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalCompleteSeedBounds.accepted_uniform_joint
  obtain ⟨P,e,hCharges⟩ := accepted_uniform_charges
  refine ⟨C+P,max d e,?_⟩
  intro frame parsed hParsed rich seed
  have ho := hOld frame parsed hParsed rich seed
  have hc := hCharges frame parsed hParsed rich seed
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  change (runWithCharges frame parsed hParsed rich seed).1.2+
    BinaryBigEndian.littleValue (runWithCharges frame parsed hParsed rich seed).1.1.1.2+
    usage (runWithCharges frame parsed hParsed rich seed).1.1.2 ≤ C*(frame.length+1)^d at ho
  dsimp only
  nlinarith only [ho,hc,hd,he]

theorem accepted_scalar_width : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    let produced := runWithCharges frame parsed hParsed rich seed
    ∀ counter ∈ [produced.1.2,produced.2.execution.primitive,produced.2.execution.coinSource,
      produced.2.execution.write,produced.2.execution.native,produced.2.execution.wrappers,produced.2.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  let produced := runWithCharges frame parsed hParsed rich seed
  have hb := hBound frame parsed hParsed rich seed
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

theorem accepted_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool)
    (held : Held parsed.1.2.logical)
    (hPrepared : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 = some held) :
    let incoming := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed held.2.1 rich
      parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
    let produced := runWithCharges frame parsed hParsed rich seed
    produced.2.execution.primitive = incoming.2.primitive ∧
      produced.2.execution.coinSource = incoming.2.coinSource ∧
      produced.2.execution.write = incoming.2.write ∧ produced.2.execution.native = incoming.2.native := by
  unfold runWithCharges
  simp only [BinarySeedPreparationEmission.prepare_compat,hPrepared]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rejected_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool)
    (hPrepared : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 = none) :
    let produced := runWithCharges frame parsed hParsed rich seed
    produced.2.execution.primitive = 0 ∧ produced.2.execution.coinSource = 0 ∧
      produced.2.execution.write = 0 ∧ produced.2.execution.native = 0 := by
  unfold runWithCharges
  simp only [BinarySeedPreparationEmission.prepare_compat,hPrepared]
  exact ⟨rfl,rfl,rfl,rfl⟩

end Blotto.BinaryCompleteSeedCharges
