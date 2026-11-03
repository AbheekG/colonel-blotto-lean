import Blotto.BinaryTerminalDispatchArithmeticEntryWork
import Blotto.BinaryResourceRequestEntryWork

/-! Complete cache-to-output raw/comparison entry accounting consumes the
actual certified cache, terminal choice and returned output row. Global
fallback borrows budget/zero words and adds no raw/comparison entry calls. -/
namespace Blotto.BinaryCacheCompleteArithmeticEntryWork
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
  BinaryResourceArithmeticEntryWork.cache parsed.1 seed rich+
    match hs : observed.1.1.1.1 with
    | none => 0
    | some result => BinaryTerminalDispatchArithmeticEntryWork.terminal seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
            (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs))) K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
          (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))

theorem draw_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    draw frame parsed hParsed seed rich K outer scalar ≤
      2*listCells (BinaryCacheFinishRequest.draw frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified BinaryCacheFinishRequest.backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  have hc := BinaryResourceRequestEntryWork.certified_bound frame parsed hParsed seed rich
  dsimp only [BinaryCacheFinishRequest.certified] at hc
  unfold draw
  simp only [BinaryCacheFinishRequest.draw,BinaryCacheContinuationCore.draw_record]
  split
  · rename_i hNone
    split
    · simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]; omega
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
      have ht := BinaryTerminalDispatchArithmeticEntryWork.terminal_bound seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
            (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs))) K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
          (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
      dsimp only [request,observed,returned,child] at ht
      simp only [BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ℕ := draw frame parsed hParsed seed rich K outer scalar

theorem fixed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixed frame parsed hParsed seed rich K outer scalar ≤
      2*listCells (BinaryCacheFinishRequest.fixed frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  have hd := draw_bound frame parsed hParsed seed rich K outer scalar
  dsimp only [BinaryCacheFinishRequest.draw] at hd
  simp only [fixed,BinaryCacheFinishRequest.fixed,BinaryCacheContinuationCore.fixed_record]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
    wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : ℕ :=
  let child := BinaryCacheContinuationCore.fixed BinaryCacheFinishRequest.backend frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let drawn := returned.1
  fixed frame parsed hParsed seed rich K outer scalar+
    BinaryPhysicalArithmeticEntryWork.output parsed.1.2.logical.request.prepared.original.a drawn.1.1.1.1.data.toList

theorem framed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framed frame parsed hParsed seed rich K outer scalar header ≤
      2*listCells (BinaryCacheFinishRequest.framed frame parsed hParsed seed rich K outer scalar header).1.1.1.2 := by
  have hf := fixed_bound frame parsed hParsed seed rich K outer scalar
  have ho := BinaryPhysicalArithmeticEntryWork.output_bound parsed.1.2.logical.request.prepared.original.a header.bytes
    (BinaryCacheContinuationCore.fixed BinaryCacheFinishRequest.backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.1.data.toList
  dsimp only [BinaryCacheFinishRequest.fixed] at hf
  simp only [framed,BinaryCacheFinishRequest.framed,BinaryCacheContinuationCore.framed_record,
    BinaryWrapperEmission.listTwo_trace,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
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
    seedCost frame parsed hParsed rich bits ≤ 2*listCells (BinaryCacheFinishRequest.seed frame parsed hParsed rich bits).1.1.1.2 := by
  simp only [seedCost,BinaryCacheFinishRequest.seed_record,BinaryCacheContinuationCore.seed_record]
  split
  · rename_i hNone
    simp only [hNone]; omega
  · rename_i held hSome
    have h := framed_bound frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header
    dsimp only [BinaryCacheFinishRequest.framed] at h
    simp only [hSome,BinarySeedWrapperEmission.nested_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega

end Blotto.BinaryCacheCompleteArithmeticEntryWork
