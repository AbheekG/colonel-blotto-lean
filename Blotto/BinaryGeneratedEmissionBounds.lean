import Blotto.BinaryCompleteGeneratedCharges

/-! Actual generation emission reaches complete single/pair execution in its
own field. The preceding full sampler records and ledgers are exact projections.
The original source/primitive and entropy models remain explicit. -/
namespace Blotto.BinaryGeneratedEmissionBounds
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryGenerationExecutionCharges
open BinaryTerminalPhysicalCompleteGeneratedMeasured
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem run_record {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (runWithGeneration next rich frame state).1 = (runWithCharges next rich frame state).1 := rfl

theorem run_sampler {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (runWithGeneration next rich frame state).2.sampler = (runWithCharges next rich frame state).2 := rfl

theorem pair_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithGeneration next frame state).1 = (pairWithCharges next frame state).1 := rfl

theorem pair_sampler {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithGeneration next frame state).2.sampler = (pairWithCharges next frame state).2 := rfl

theorem accepted_generation {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (runWithGeneration next rich frame state).2.generationEmission =
      (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).2 := by
  unfold runWithGeneration
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_left hTail]
    rfl

theorem rejected_none_generation {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    (runWithGeneration next rich frame state).2.generationEmission = 0 := by
  unfold runWithGeneration
  dsimp only
  split
  · rfl
  · rename_i selected hSome
    cases hParsed.symm.trans hSome

theorem rejected_tail_generation {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    (runWithGeneration next rich frame state).2.generationEmission = 0 := by
  unfold runWithGeneration
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_right hTail]
    rfl

theorem uniform_generation {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (runWithGeneration next rich frame state).2.generationEmission ≤ 9600000*(frame.length+1) := by
  cases hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none => rw [rejected_none_generation next rich frame state hRead]; exact Nat.zero_le _
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · rw [accepted_generation next rich frame state parsed hRead hTail]
        exact BinaryFreshGenerationPlan.physical_emission_linear next frame parsed hRead state
      · rw [rejected_tail_generation next rich frame state parsed hRead hTail]; exact Nat.zero_le _

theorem accepted_total {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    total (runWithGeneration next rich frame state).2 =
      BinarySamplerExecutionCharges.total (runWithCharges next rich frame state).2+
      (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).2 := by
  rw [total,run_sampler,accepted_generation next rich frame state parsed hParsed hTail]

theorem parsed_generation {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state).2.generationEmission =
      (runWithGeneration next rich frame state).2.generationEmission := by
  unfold BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration runWithGeneration
  dsimp only
  split
  · rename_i hNone
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hNone
    split
    · rfl
    · rename_i parsed hSome
      cases hOld.symm.trans hSome
  · rename_i parsed hSome
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hSome
    symm
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hOld.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail]
        rfl
      · simp only [ite_eq_right hTail]
        rfl

theorem pair_generation {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithGeneration next frame state).2.generationEmission =
      (runWithGeneration next true frame state).2.generationEmission+
      (runWithGeneration next false frame (run next true frame state).1.1.1.2).2.generationEmission := rfl

theorem pair_uniform_generation {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithGeneration next frame state).2.generationEmission ≤ 19200000*(frame.length+1) := by
  have hr := uniform_generation next true frame state
  have hp := uniform_generation next false frame (run next true frame state).1.1.1.2
  rw [pair_generation]
  omega

theorem parsed_pair_generation {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state).2.generationEmission =
      (pairWithGeneration next frame state).2.generationEmission := by
  change (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next true frame state).2.generationEmission+
    (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next false frame
      (BinaryTerminalPhysicalParsedGeneratedMeasured.run next true frame state).1.1.1.2).2.generationEmission = _
  rw [parsed_generation,parsed_generation,BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases]
  rfl

theorem parsed_uniform_generation {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state).2.generationEmission ≤
      9600000*(frame.length+1) := by
  rw [parsed_generation]
  exact uniform_generation next rich frame state

theorem parsed_pair_uniform_generation {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state).2.generationEmission ≤
      19200000*(frame.length+1) := by
  rw [parsed_pair_generation]
  exact pair_uniform_generation next frame state

theorem uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteGeneratedCharges.uniform_joint
  refine ⟨C+9600000,max d 1,?_⟩
  intro S next rich frame state
  let produced := BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state
  have ho := hOld next rich frame state
  have hg := uniform_generation next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : frame.length+1 ≤ (frame.length+1)^(max d 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+
    BinarySamplerExecutionCharges.total produced.2.sampler ≤ _ at ho
  change produced.2.generationEmission ≤ _ at hg
  dsimp only
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ _
  dsimp only [total]
  nlinarith only [ho,hg,hd,hLinear]

theorem pair_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteGeneratedCharges.pair_uniform_joint
  refine ⟨C+19200000,max d 1,?_⟩
  intro S next frame state
  let produced := BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state
  have ho := hOld next frame state
  have hg := pair_uniform_generation next frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : frame.length+1 ≤ (frame.length+1)^(max d 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+
    BinarySamplerExecutionCharges.total produced.2.sampler ≤ _ at ho
  change produced.2.generationEmission ≤ _ at hg
  dsimp only
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ _
  dsimp only [total]
  nlinarith only [ho,hg,hd,hLinear]

theorem parsed_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteGeneratedCharges.parsed_uniform_joint
  refine ⟨C+9600000,max d 1,?_⟩
  intro S next rich frame state
  let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state
  have ho := hOld next rich frame state
  have hg := parsed_uniform_generation next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : frame.length+1 ≤ (frame.length+1)^(max d 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+
    BinarySamplerExecutionCharges.total produced.2.sampler ≤ _ at ho
  change produced.2.generationEmission ≤ _ at hg
  dsimp only
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ _
  dsimp only [total]
  nlinarith only [ho,hg,hd,hLinear]

theorem parsed_pair_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteGeneratedCharges.parsed_pair_uniform_joint
  refine ⟨C+19200000,max d 1,?_⟩
  intro S next frame state
  let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state
  have ho := hOld next frame state
  have hg := parsed_pair_uniform_generation next frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : frame.length+1 ≤ (frame.length+1)^(max d 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+
    BinarySamplerExecutionCharges.total produced.2.sampler ≤ _ at ho
  change produced.2.generationEmission ≤ _ at hg
  dsimp only
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ _
  dsimp only [total]
  nlinarith only [ho,hg,hd,hLinear]

theorem counter_width (source allowance retained : ℕ) (charges : Charges) (L C d : ℕ)
    (hBound : source+allowance+retained+total charges ≤ C*(L+1)^d) :
    ∀ counter ∈ [source,charges.sampler.execution.primitive,charges.sampler.execution.coinSource,
      charges.sampler.execution.write,charges.sampler.execution.native,charges.sampler.execution.wrappers,
      charges.sampler.seedEmission,charges.generationEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (L+1) := by
  have hf := fields_le_total charges
  have hm := binaryWordWidth_mul C ((L+1)^d)
  have hp := Farey.binaryWordWidth_power (L+1) d
  have hWidth := binaryWordWidth_mono hBound
  intro counter hCounter
  have hc : counter ≤ source+allowance+retained+total charges := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  omega

theorem parsed_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state
    ∀ counter ∈ [produced.1.2,produced.2.sampler.execution.primitive,produced.2.sampler.execution.coinSource,
      produced.2.sampler.execution.write,produced.2.sampler.execution.native,produced.2.sampler.execution.wrappers,
      produced.2.sampler.seedEmission,produced.2.generationEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsed_uniform_joint
  exact ⟨C,d,fun next rich frame state => counter_width _ _ _ _ _ C d (hBound next rich frame state)⟩

theorem parsed_pair_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state
    ∀ counter ∈ [produced.1.2,produced.2.sampler.execution.primitive,produced.2.sampler.execution.coinSource,
      produced.2.sampler.execution.write,produced.2.sampler.execution.native,produced.2.sampler.execution.wrappers,
      produced.2.sampler.seedEmission,produced.2.generationEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsed_pair_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact counter_width _ (_+_) _ _ _ C d (by simpa only [Nat.add_assoc] using hBound next frame state)

end Blotto.BinaryGeneratedEmissionBounds
