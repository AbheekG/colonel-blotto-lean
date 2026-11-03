import Blotto.BinaryTerminalTraceSparsity
import Blotto.BinaryPhysicalOutputTraceSparsity
import Blotto.BinaryCertifiedFramedCharges

/-! The complete measured terminal, fallback and physical output pay their
actual event counts from allocated source cells. The certified front remains
explicit and is bounded separately at its original accepted-input scope. -/
namespace Blotto.BinaryCompleteFramedTraceBounds
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem one_relative (slots frames : ℕ) (front : Trace) (hSlots : 1 ≤ slots) :
    (wrap slots frames [front]).length+3*cells front ≤ front.length+3*cells (wrap slots frames [front]) := by
  simp only [wrap,combine,List.length_append,under_length,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,List.length_cons,List.length_nil]
  omega

theorem two_relative (slots frames : ℕ) (front tail : Trace) (hSlots : 2 ≤ slots) (hTail : Bounded tail) :
    (wrap slots frames [front,tail]).length+3*cells front ≤ front.length+3*cells (wrap slots frames [front,tail]) := by
  unfold Bounded at hTail
  simp only [wrap,combine,List.length_append,under_length,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,List.length_cons,List.length_nil] at *
  omega

theorem list_two_relative (allocated slots frames : ℕ) (front tail : Trace) (hSlots : 2 ≤ slots) (hTail : Bounded tail) :
    (wrapList allocated slots frames [front,tail]).length+3*cells front ≤
      front.length+3*cells (wrapList allocated slots frames [front,tail]) := by
  unfold Bounded at hTail
  simp only [wrapList,wrap,combine,List.length_append,under_length,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,List.length_cons,List.length_nil] at *
  omega

theorem draw_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.2.length+
        3*cells (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2 ≤
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length+
        3*cells (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.2 := by
  rw [BinaryTerminalPhysicalCompleteDrawMeasured.run_eq_reference]
  unfold BinaryTerminalPhysicalCompleteDrawMeasured.runReference
  dsimp only
  split
  · exact one_relative 16 2 _ (by decide)
  · exact two_relative 32 2 _ _ (by decide) (BinaryTerminalTraceSparsity.terminal_bound _ _ _ _ _ _ _ _ _)

theorem fixed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar).1.2.length+
        3*cells (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.2 ≤
      (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.2.length+
        3*cells (BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar).1.2 := by
  rw [BinaryTerminalPhysicalCompleteFixedMeasured.run_eq_reference]
  unfold BinaryTerminalPhysicalCompleteFixedMeasured.runReference
  dsimp only
  split
  · exact one_relative 24 2 _ (by decide)
  · exact two_relative 32 2 _ _ (by decide) (BinaryPhysicalOutputTraceSparsity.fallback_bound _)

theorem framed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header).1.2.length+
        3*cells (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2 ≤
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length+
        3*cells (BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header).1.2 := by
  have hd := draw_relative frame parsed hParsed seed rich K outer scalar
  have hf := fixed_relative frame parsed hParsed seed rich K outer scalar
  have hp := list_two_relative parsed.1.1 32 (parsed.1.1+2)
    (BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar).1.2
    (BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a header.bytes
      (BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar).1.1.1.1.data.toList).1.2
    (by decide) (BinaryPhysicalOutputTraceSparsity.output_bound _ _ _)
  rw [BinaryTerminalPhysicalCompleteFramedMeasured.run_eq_reference]
  unfold BinaryTerminalPhysicalCompleteFramedMeasured.runReference
  dsimp only
  omega

theorem framed_length (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header).1.2.length ≤
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2.length+
        3*usage (BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed seed rich K outer scalar header).1.2 := by
  have h := framed_relative frame parsed hParsed seed rich K outer scalar header
  unfold usage cells at *
  omega

end Blotto.BinaryCompleteFramedTraceBounds
