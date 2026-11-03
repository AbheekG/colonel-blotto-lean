import Blotto.BinaryTerminalReflectedExtraWork
import Blotto.BinaryResourceRequestEntryWork

/-! Actual accepted cache/terminal results carry reached reflected primitive
and initializer extra work/allocated-bit charges through global fallback,
output and seed validation. Complete source/trace ceilings yield an unconditional
original-frame polynomial for this additional charge class. -/
namespace Blotto.BinaryCacheReflectedExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork
set_option autoImplicit false
set_option maxHeartbeats 5000000

def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ℕ :=
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified BinaryCacheFinishRequest.backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  match hs : observed.1.1.1.1 with
    | none => 0
    | some result => BinaryTerminalReflectedExtraWork.terminal seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
            (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs))) K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
          (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))

theorem draw_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    draw frame parsed hParsed seed rich K outer scalar ≤
      49*(BinaryCacheFinishRequest.draw frame parsed hParsed seed rich K outer scalar).1.1.2+35*(BinaryCacheFinishRequest.draw frame parsed hParsed seed rich K outer scalar).1.1.1.2.length+475 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified BinaryCacheFinishRequest.backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  unfold draw
  simp only [BinaryCacheFinishRequest.draw,BinaryCacheContinuationCore.draw_record]
  split
  · rename_i hNone
    split
    · simp only [BinaryWrapperEmission.one_length,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; omega
    · rename_i other hSome
      rw [hNone] at hSome
      cases hSome
  · rename_i result hs
    split
    · rename_i hNone
      rw [hNone] at hs
      cases hs
    · rename_i other hOther
      have hEq : other=result := Option.some.inj (hOther.symm.trans hs)
      subst other
      change observed.1.1.1.1=some result at hs
      have ht := BinaryTerminalReflectedExtraWork.terminal_bound seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
            (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs))) K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
          (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
      dsimp only [request,observed,returned,child] at ht
      simp only [BinaryWrapperEmission.two_length,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ℕ := draw frame parsed hParsed seed rich K outer scalar

theorem fixed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixed frame parsed hParsed seed rich K outer scalar ≤
      49*(BinaryCacheFinishRequest.fixed frame parsed hParsed seed rich K outer scalar).1.1.2+35*(BinaryCacheFinishRequest.fixed frame parsed hParsed seed rich K outer scalar).1.1.1.2.length+475 := by
  have hd := draw_bound frame parsed hParsed seed rich K outer scalar
  dsimp only [BinaryCacheFinishRequest.draw] at hd
  simp only [fixed,BinaryCacheFinishRequest.fixed,BinaryCacheContinuationCore.fixed_record]
  split <;> simp only [BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length,
    BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> omega

def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : ℕ :=
  fixed frame parsed hParsed seed rich K outer scalar

theorem framed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framed frame parsed hParsed seed rich K outer scalar header ≤
      49*(BinaryCacheFinishRequest.framed frame parsed hParsed seed rich K outer scalar header).1.1.2+35*(BinaryCacheFinishRequest.framed frame parsed hParsed seed rich K outer scalar header).1.1.1.2.length+475 := by
  have hf := fixed_bound frame parsed hParsed seed rich K outer scalar
  dsimp only [BinaryCacheFinishRequest.fixed] at hf
  simp only [framed,BinaryCacheFinishRequest.framed,BinaryCacheContinuationCore.framed_record,
    BinaryWrapperEmission.listTwo_length]
  omega

def seedCost (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) : ℕ :=
  match (BinarySeedPreparationEmission.prepare parsed.1.2.logical bits).1.1.1 with
  | none => 0
  | some held => framed frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header

theorem seed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    seedCost frame parsed hParsed rich bits ≤ 49*(BinaryCacheFinishRequest.seed frame parsed hParsed rich bits).1.1.2+35*(BinaryCacheFinishRequest.seed frame parsed hParsed rich bits).1.1.1.2.length+475 := by
  simp only [seedCost,BinaryCacheFinishRequest.seed_record,BinaryCacheContinuationCore.seed_record]
  split
  · rename_i hNone
    simp only [hNone]; omega
  · rename_i held hSome
    have h := framed_bound frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header
    dsimp only [BinaryCacheFinishRequest.framed] at h
    simp only [hSome,BinarySeedWrapperEmission.nested_length,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega

theorem seed_uniform : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (bits : List Bool),
    seedCost frame parsed hParsed rich bits ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteSeedCharges.accepted_uniform_joint
  obtain ⟨P,e,hTrace⟩ := BinaryCompleteSeedEventBounds.accepted_trace
  refine ⟨49*C+35*P+475,max d e,?_⟩
  intro frame parsed hParsed rich bits
  have hb := seed_bound frame parsed hParsed rich bits
  rw [BinaryCacheFinishRequest.seed_compat] at hb
  have ho := hOld frame parsed hParsed rich bits
  dsimp only at ho
  have ht := hTrace frame parsed hParsed rich bits
  change (BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits).1.1.2.length ≤ _ at ht
  have hX : 0<frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) (frame.length+1) (by omega)
  nlinarith only [hb,ho,ht,hd,hp,hOne]

end Blotto.BinaryCacheReflectedExtraWork
