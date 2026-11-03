import Blotto.BinaryRequestCacheCharges
import Blotto.BinaryTerminalPhysicalCompleteFramedMeasured

/-! The complete actual cache ledger reaches certification and measured
terminal/fallback/framing execution. Certification has an accepted uniform
source/emitter bound. Later wrapper transport retains the returned trace-event
footprint explicitly; its terminal event envelope and full native prices remain
separate obligations, without weakening the complete sampler objective. -/
namespace Blotto.BinaryCertifiedFramedCharges
open BinarySeedPreparationSpace BinaryExecutionCharges
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem cache_trace_length (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).1.2.length ≤
      26*(BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).2+
        (BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
        (2^62+1)*(frame.length+3)^8+9 := by
  have h := BinaryRequestCacheCharges.run_trace_length seed parsed.1.2 rich
  rw [BinaryTerminalPhysicalAllowanceCache.run_eq_reference]
  unfold BinaryTerminalPhysicalAllowanceCache.runReference
  dsimp only
  split
  · simp only [BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,List.length_append,
      BinaryResourceTraceLength.under_length,List.length_cons,List.length_nil]
    omega
  · rename_i state hState
    have hc := BinaryRequestCacheCharges.reached_cache_length frame parsed hParsed seed rich state hState
    simp only [BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,List.length_append,
      BinaryResourceTraceLength.under_length,List.length_cons,List.length_nil]
    omega

theorem certification_trace_length (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length ≤
      (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).1.2.length+4 := by
  rw [BinaryTerminalPhysicalAllowanceCertified.run_eq_reference]
  unfold BinaryTerminalPhysicalAllowanceCertified.runReference
  dsimp only
  split <;> simp only [BinaryTerminalCacheCertificate.certifyWithTrace,
    BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,List.length_append,
    BinaryResourceTraceLength.under_length,List.length_cons,List.length_nil] <;> omega

theorem certification_total (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let produced := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
    produced.1.2+total produced.2 ≤
      618*produced.1.2+25*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
        16*parsed.1.1+223+10*((2^62+1)*(frame.length+3)^8) := by
  have hc := BinaryRequestCacheCharges.cache_total parsed.1 seed rich ((2^62+1)*(frame.length+3)^8)
    (fun state hState => BinaryRequestCacheCharges.reached_cache_length frame parsed hParsed seed rich state hState)
  have ht := cache_trace_length frame parsed hParsed seed rich
  have he := certification_trace_length frame parsed hParsed seed rich
  have hs := BinaryTerminalPhysicalAllowanceCertified.runWithCharges_step frame parsed hParsed seed rich
  have hw := BinaryTerminalPhysicalAllowanceCertified.run_carried_work frame parsed hParsed seed rich
  dsimp only at hc hs ⊢
  change (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2+
    total (BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich).2 ≤
      618*(BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2+
        25*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
          16*parsed.1.1+223+10*((2^62+1)*(frame.length+3)^8)
  change (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).2+
    total (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich).2 ≤
      488*(BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).2+
        20*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
          16*parsed.1.1+150+5*((2^62+1)*(frame.length+3)^8) at hc
  have hs1 := hs.1
  change total (BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich).2 ≤
    total (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich).2+
      5*(BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length+8 at hs1
  omega

theorem accepted_certification_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      let produced := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
      produced.1.2+total produced.2 ≤ 618*produced.1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨12*C+10*(2^62+1),max d 8,?_⟩
  intro frame parsed hParsed seed rich
  have h := certification_total frame parsed hParsed seed rich
  have ho := hOverhead frame parsed hParsed rich
  have hi : 25*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
      16*parsed.1.1+223 ≤ (12*C)*(frame.length+3)^d := by
    simp only [Nat.mul_assoc]
    omega
  have hd := Nat.mul_le_mul_left (12*C)
    (Nat.pow_le_pow_right (by omega : 0 < frame.length+3) (Nat.le_max_left d 8))
  have he := Nat.mul_le_mul_left (10*(2^62+1))
    (Nat.pow_le_pow_right (by omega : 0 < frame.length+3) (Nat.le_max_right d 8))
  dsimp only at h ⊢
  nlinarith only [h,hi,hd,he]

theorem accepted_certification_uniform : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      let produced := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
      produced.1.2+total produced.2 ≤ C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalAllowanceCertified.accepted_uniform_carried_work
  obtain ⟨P,e,hNew⟩ := accepted_certification_total
  refine ⟨618*C+P,max d e,?_⟩
  intro frame parsed hParsed seed rich
  have ho := hOld frame parsed hParsed seed rich
  have hWork : (BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich).1.2 ≤
      C*(frame.length+seed.width+seed.cap.value+3)^d := by
    change (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2 ≤ _
    omega
  exact BinaryRequestCacheCharges.uniform_envelope frame.length seed.width seed.cap.value _ _ 618 C P d e
    hWork (hNew frame parsed hParsed seed rich)

theorem framed_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let initial := (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich).2
    let charges := (BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges
      frame parsed hParsed seed rich K outer scalar header).2
    charges.primitive = initial.primitive ∧ charges.coinSource = initial.coinSource ∧
      charges.write = initial.write ∧ charges.native = initial.native := by
  have hc := BinaryTerminalPhysicalAllowanceCertified.runWithCharges_fields frame parsed hParsed seed rich
  have hd := BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges_fields frame parsed hParsed seed rich K outer scalar
  have hf := BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges_fields frame parsed hParsed seed rich K outer scalar
  have hp := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges_fields frame parsed hParsed seed rich K outer scalar header
  dsimp only at hc hd hf hp ⊢
  exact ⟨hp.1.trans (hf.1.trans (hd.1.trans hc.1)),
    hp.2.1.trans (hf.2.1.trans (hd.2.1.trans hc.2.1)),
    hp.2.2.1.trans (hf.2.2.1.trans (hd.2.2.1.trans hc.2.2.1)),
    hp.2.2.2.trans (hf.2.2.2.trans (hd.2.2.2.trans hc.2.2.2))⟩

theorem framed_from_certification (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let initial := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
    let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges
      frame parsed hParsed seed rich K outer scalar header
    total produced.2 ≤ total initial.2+15*produced.1.1.2.length+24 ∧
      initial.1.1.2.length ≤ produced.1.1.2.length ∧ initial.1.2 ≤ produced.1.2 := by
  have hd := BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges_step frame parsed hParsed seed rich K outer scalar
  have hf := BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges_step frame parsed hParsed seed rich K outer scalar
  have hp := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges_step frame parsed hParsed seed rich K outer scalar header
  dsimp only at hd hf hp ⊢
  omega

theorem accepted_framed_footprint : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges
        frame parsed hParsed seed rich K outer scalar header
      produced.1.2+total produced.2 ≤ 618*produced.1.2+15*produced.1.1.2.length+C*(frame.length+3)^d := by
  obtain ⟨C,d,hCertified⟩ := accepted_certification_total
  refine ⟨C+24,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  have hc := hCertified frame parsed hParsed seed rich
  have hf := framed_from_certification frame parsed hParsed seed rich K outer scalar header
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  dsimp only at hc hf ⊢
  nlinarith only [hc,hf.1,hf.2.2,hOne]

theorem accepted_certification_scalar_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      let produced := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
      ∀ counter ∈ [produced.1.2,produced.2.primitive,produced.2.coinSource,
        produced.2.write,produced.2.native,produced.2.wrappers],
        binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth
          (frame.length+seed.width+seed.cap.value+3) := by
  obtain ⟨C,d,hBound⟩ := accepted_certification_uniform
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  let produced := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
  have hb := hBound frame parsed hParsed seed rich
  have hf := fields_le_total produced.2
  dsimp only [produced] at hf
  have hm := binaryWordWidth_mul C ((frame.length+seed.width+seed.cap.value+3)^d)
  have hp := Farey.binaryWordWidth_power (frame.length+seed.width+seed.cap.value+3) d
  have hWidth := binaryWordWidth_mono hb
  dsimp only
  intro counter hCounter
  have hc : counter ≤ produced.1.2+total produced.2 := by
    dsimp only [produced]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  dsimp only [produced] at hw
  omega

end Blotto.BinaryCertifiedFramedCharges
