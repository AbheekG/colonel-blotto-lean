import Blotto.BinaryCompleteFramedTraceBounds

/-! Uniform source/charge/usage bounds for the complete actual framed producer.
The preceding named charges retain their meanings. Numerical seed-cap access
and complete native machine prices remain at their explicitly inherited scope. -/
namespace Blotto.BinaryCompleteFramedCharges
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryExecutionCharges
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem accepted_certification_trace : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length ≤
        26*(BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hInitial⟩ := BinaryInitialTraceSparsity.accepted_initial_length
  refine ⟨C+(2^62+1)+13,max d 8,?_⟩
  intro frame parsed hParsed seed rich
  have hi := hInitial frame parsed hParsed rich
  have hc := BinaryCertifiedFramedCharges.cache_trace_length frame parsed hParsed seed rich
  have ht := BinaryCertifiedFramedCharges.certification_trace_length frame parsed hParsed seed rich
  have hw := BinaryTerminalPhysicalAllowanceCertified.run_carried_work frame parsed hParsed seed rich
  have hd := Nat.pow_le_pow_right (show 0 < frame.length+3 by omega) (Nat.le_max_left d 8)
  have he := Nat.pow_le_pow_right (show 0 < frame.length+3 by omega) (Nat.le_max_right d 8)
  have hOne := Nat.one_le_pow (max d 8) (frame.length+3) (by omega)
  have hp := Nat.mul_le_mul_left C hd
  have hq := Nat.mul_le_mul_left (2^62+1) he
  nlinarith only [hi,hc,ht,hw,hOne,hp,hq]

theorem accepted_framed_trace_footprint : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      let produced := BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header
      produced.1.2.length ≤ 26*produced.2+3*usage produced.1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hCertified⟩ := accepted_certification_trace
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  have hc := hCertified frame parsed hParsed seed rich
  have ht := BinaryCompleteFramedTraceBounds.framed_length frame parsed hParsed seed rich K outer scalar header
  have hw := (BinaryCertifiedFramedCharges.framed_from_certification frame parsed hParsed seed rich K outer scalar header).2.2
  change (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2 ≤
    (BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header).2 at hw
  dsimp only
  omega

theorem accepted_uniform_joint : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header
      produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤
        C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨W,e,hWork⟩ := BinaryTerminalPhysicalCompleteFramedMeasured.accepted_uniform_joint
  obtain ⟨T,f,hTrace⟩ := accepted_framed_trace_footprint
  obtain ⟨F,g,hCharge⟩ := BinaryCertifiedFramedCharges.accepted_framed_footprint
  refine ⟨1008*W+15*T+F,max e (max f g),?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let Q := frame.length+K+seed.width+seed.cap.value+header.bytes.length+3
  let D := max e (max f g)
  let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hL : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have hw := hWork frame parsed hParsed seed rich K outer scalar header
  have ht := hTrace frame parsed hParsed seed rich K outer scalar header
  have hc := hCharge frame parsed hParsed seed rich K outer scalar header
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2 ≤ W*Q^e at hw
  change produced.1.1.2.length ≤ 26*produced.1.2+3*usage produced.1.1.2+T*(frame.length+3)^f at ht
  change produced.1.2+total produced.2 ≤ 618*produced.1.2+15*produced.1.1.2.length+F*(frame.length+3)^g at hc
  have hWe : Q^e ≤ Q^D := Nat.pow_le_pow_right hQ (Nat.le_max_left _ _)
  have hTf : (frame.length+3)^f ≤ Q^D := (Nat.pow_le_pow_left hL f).trans
    (Nat.pow_le_pow_right hQ ((Nat.le_max_left f g).trans (Nat.le_max_right e _)))
  have hFg : (frame.length+3)^g ≤ Q^D := (Nat.pow_le_pow_left hL g).trans
    (Nat.pow_le_pow_right hQ ((Nat.le_max_right f g).trans (Nat.le_max_right e _)))
  have hW := Nat.mul_le_mul_left W hWe
  have hT := Nat.mul_le_mul_left T hTf
  have hF := Nat.mul_le_mul_left F hFg
  change produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤
    (1008*W+15*T+F)*Q^D
  nlinarith only [hw,ht,hc,hW,hT,hF]

theorem accepted_uniform_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header
      produced.1.2+total produced.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  have hb := h frame parsed hParsed seed rich K outer scalar header
  dsimp only at hb ⊢
  omega

theorem accepted_scalar_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header
      ∀ counter ∈ [produced.1.2,produced.2.primitive,produced.2.coinSource,
        produced.2.write,produced.2.native,produced.2.wrappers],
        binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth
          (frame.length+K+seed.width+seed.cap.value+header.bytes.length+3) := by
  obtain ⟨C,d,hBound⟩ := accepted_uniform_total
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let produced := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header
  have hb := hBound frame parsed hParsed seed rich K outer scalar header
  have hf := fields_le_total produced.2
  dsimp only [produced] at hf
  have hm := binaryWordWidth_mul C ((frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d)
  have hp := Farey.binaryWordWidth_power (frame.length+K+seed.width+seed.cap.value+header.bytes.length+3) d
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

end Blotto.BinaryCompleteFramedCharges
