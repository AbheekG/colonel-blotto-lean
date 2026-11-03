import Blotto.BinaryInitializerEmissionExecution

/-! The actual initializer-calculator emission has a relative source-work
bound and global original-frame bounds through complete raw/generated single
and consecutive pair execution. Both prior cache emission and all preceding
ledgers retain their meaning. Native machine/whole-space joins remain open. -/
namespace Blotto.BinaryInitializerEmissionBounds
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryInitializerEmissionExecution BinaryPRGTerminalWork
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] BinaryInitializerEmissionExecution.seed

theorem cache_relative (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).2.2 ≤ 50*(cache parsed seed rich).1.1.2+5 := by
  have h := BinaryAllowanceEmissionRequest.runWithCharges_bound seed parsed.2 rich
  unfold cache
  dsimp only
  split <;> dsimp only <;> omega

theorem certified_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).2.2 ≤ 50*(certified frame parsed hParsed seed rich).1.1.2+5 := by
  have he := cache_relative parsed.1 seed rich
  have hm : (cache parsed.1 seed rich).1.1.2 ≤
      (certified frame parsed hParsed seed rich).1.1.2 := by
    unfold certified
    dsimp only
    split <;> dsimp only <;> omega
  change (cache parsed.1 seed rich).2.2 ≤ _
  omega

theorem draw_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).2.2 ≤
      50*(draw frame parsed hParsed seed rich K outer scalar).1.1.2+5 := by
  have he := certified_relative frame parsed hParsed seed rich
  have hm : (certified frame parsed hParsed seed rich).1.1.2 ≤
      (draw frame parsed hParsed seed rich K outer scalar).1.1.2 := by
    unfold draw
    dsimp only
    split <;> dsimp only <;> omega
  change (certified frame parsed hParsed seed rich).2.2 ≤ _
  omega

theorem fixed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).2.2 ≤
      50*(fixed frame parsed hParsed seed rich K outer scalar).1.1.2+5 := by
  have he := draw_relative frame parsed hParsed seed rich K outer scalar
  have hm : (draw frame parsed hParsed seed rich K outer scalar).1.1.2 ≤
      (fixed frame parsed hParsed seed rich K outer scalar).1.1.2 := by
    unfold fixed
    dsimp only
    split <;> dsimp only <;> omega
  change (draw frame parsed hParsed seed rich K outer scalar).2.2 ≤ _
  omega

theorem framed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).2.2 ≤
      50*(framed frame parsed hParsed seed rich K outer scalar header).1.1.2+5 := by
  have he := fixed_relative frame parsed hParsed seed rich K outer scalar
  have hm : (fixed frame parsed hParsed seed rich K outer scalar).1.1.2 ≤
      (framed frame parsed hParsed seed rich K outer scalar header).1.1.2 := by
    dsimp only [framed]
    omega
  change (fixed frame parsed hParsed seed rich K outer scalar).2.2 ≤ _
  omega

theorem seed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits).2.2 ≤
      50*(BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits).1.1.2+5 := by
  unfold BinaryInitializerEmissionExecution.seed
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i held hSome
    have he := framed_relative frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header
    dsimp only
    omega

theorem uniform_seed : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (bits : List Bool),
    (BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteSeedCharges.accepted_uniform_joint
  refine ⟨50*C+5,d,?_⟩
  intro frame parsed hParsed rich bits
  have he := seed_relative frame parsed hParsed rich bits
  rw [seed_compat] at he
  have hj := hJoint frame parsed hParsed rich bits
  dsimp only at hj
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  nlinarith only [he,hj,hOne]

theorem raw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    (raw rich frame bits).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro rich frame bits
  unfold raw
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · exact hSeed frame parsed hRead rich bits
    · exact Nat.zero_le _

theorem parsedRaw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    (parsedRaw rich frame bits).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro rich frame bits
  unfold parsedRaw
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · exact hSeed frame parsed ((congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead) rich bits
    · exact Nat.zero_le _

theorem generated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (generated next rich frame state).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold generated
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · exact hSeed frame parsed hRead rich _
    · exact Nat.zero_le _

theorem parsedGenerated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (parsedGenerated next rich frame state).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold parsedGenerated
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · exact hSeed frame parsed ((congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead) rich _
    · exact Nat.zero_le _

theorem pair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    (pair next frame state).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := generated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (generated next true frame state).1.1.1.1.1.2
  change (generated next true frame state).2.2+
    (generated next false frame (generated next true frame state).1.1.1.1.1.2).2.2 ≤ _
  nlinarith only [hr,hp]

theorem parsedPair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    (parsedPair next frame state).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := parsedGenerated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (parsedGenerated next true frame state).1.1.1.1.1.2
  change (parsedGenerated next true frame state).2.2+
    (parsedGenerated next false frame (parsedGenerated next true frame state).1.1.1.1.1.2).2.2 ≤ _
  nlinarith only [hr,hp]

theorem raw_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := raw rich frame bits
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.raw_joint
  obtain ⟨P,e,hEmission⟩ := raw_uniform
  refine ⟨C+P,max d e,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  dsimp only at ho
  simp only [← raw_preceding,preceding] at ho
  have he := hEmission rich frame bits
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedRaw_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := parsedRaw rich frame bits
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.parsedRaw_joint
  obtain ⟨P,e,hEmission⟩ := parsedRaw_uniform
  refine ⟨C+P,max d e,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  dsimp only at ho
  simp only [← parsedRaw_preceding,preceding] at ho
  have he := hEmission rich frame bits
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem generated_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := generated next rich frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.generated_joint
  obtain ⟨P,e,hEmission⟩ := generated_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  dsimp only at ho
  simp only [← generated_preceding,preceding] at ho
  have he := hEmission next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedGenerated_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := parsedGenerated next rich frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.parsedGenerated_joint
  obtain ⟨P,e,hEmission⟩ := parsedGenerated_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  dsimp only at ho
  simp only [← parsedGenerated_preceding,preceding] at ho
  have he := hEmission next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem pair_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := pair next frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.pair_joint
  obtain ⟨P,e,hEmission⟩ := pair_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  dsimp only at ho
  simp only [← pair_preceding,preceding] at ho
  have he := hEmission next frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedPair_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := parsedPair next frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1+produced.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCacheEmissionBounds.parsedPair_joint
  obtain ⟨P,e,hEmission⟩ := parsedPair_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  dsimp only at ho
  simp only [← parsedPair_preceding,preceding] at ho
  have he := hEmission next frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem counter_width (source allowance retained : ℕ) (prior : BinaryGenerationExecutionCharges.Charges)
    (cacheEmission initializerEmission L C d : ℕ)
    (hBound : source+allowance+retained+BinaryGenerationExecutionCharges.total prior+cacheEmission+initializerEmission ≤ C*(L+1)^d) :
    ∀ counter ∈ [source,prior.sampler.execution.primitive,prior.sampler.execution.coinSource,prior.sampler.execution.write,
      prior.sampler.execution.native,prior.sampler.execution.wrappers,prior.sampler.seedEmission,prior.generationEmission,
      cacheEmission,initializerEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (L+1) := by
  have hf := BinaryGenerationExecutionCharges.fields_le_total prior
  have hm := binaryWordWidth_mul C ((L+1)^d)
  have hp := Farey.binaryWordWidth_power (L+1) d
  have hWidth := binaryWordWidth_mono hBound
  intro counter hCounter
  have hc : counter ≤ source+allowance+retained+BinaryGenerationExecutionCharges.total prior+cacheEmission+initializerEmission := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  omega

theorem parsedGenerated_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := parsedGenerated next rich frame state
    ∀ counter ∈ [produced.1.1.2,produced.1.2.sampler.execution.primitive,produced.1.2.sampler.execution.coinSource,
      produced.1.2.sampler.execution.write,produced.1.2.sampler.execution.native,produced.1.2.sampler.execution.wrappers,
      produced.1.2.sampler.seedEmission,produced.1.2.generationEmission,produced.2.1,produced.2.2],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsedGenerated_joint
  exact ⟨C,d,fun next rich frame state => counter_width _ _ _ _ _ _ _ C d (hBound next rich frame state)⟩

theorem parsedPair_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := parsedPair next frame state
    ∀ counter ∈ [produced.1.1.2,produced.1.2.sampler.execution.primitive,produced.1.2.sampler.execution.coinSource,
      produced.1.2.sampler.execution.write,produced.1.2.sampler.execution.native,produced.1.2.sampler.execution.wrappers,
      produced.1.2.sampler.seedEmission,produced.1.2.generationEmission,produced.2.1,produced.2.2],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsedPair_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact counter_width _ (_+_) _ _ _ _ _ C d (by simpa only [Nat.add_assoc] using hBound next frame state)

end Blotto.BinaryInitializerEmissionBounds
