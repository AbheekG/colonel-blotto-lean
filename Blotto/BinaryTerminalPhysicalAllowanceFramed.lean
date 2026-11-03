import Blotto.BinaryTerminalPhysicalAllowanceDraw
import Blotto.BinaryTerminalPhysicalFramedLifetime

/-! Global exhaustion fallback and direct physical framing continue the
Boolean-allowance route. The work field still carries cache-prefix work;
the allocation trace includes the later producers. No terminal-runtime claim
is inferred from the carried prefix charge. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceFramed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGResourceWork
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) ×
      Trace) × ℕ) :=
  let drawn := BinaryTerminalPhysicalAllowanceDraw.run
    frame parsed hParsed seed rich K outer scalar
  match drawn.1.1.1.1 with
  | some row =>
      ((((row,drawn.1.1.1.2),drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2)
  | none =>
      let fallback := BinaryPRGGlobalFallbackLifetime.prepareWithTrace
        (resourceInput parsed.1.2.logical.request rich)
      ((((fallback.1,drawn.1.1.1.2),drawn.1.1.2),
        wrap 32 2 [drawn.1.2,fallback.2]),drawn.2)

theorem fixed_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1.1.1 =
      (BinaryTerminalPhysicalFixedLifetime.runWithTrace
        frame parsed hParsed seed rich K outer scalar).1 := by
  unfold fixed BinaryTerminalPhysicalFixedLifetime.runWithTrace
  dsimp only
  simp only [BinaryTerminalPhysicalAllowanceDraw.run_data]
  cases h : (BinaryTerminalPhysicalDrawLifetime.runWithTrace
    frame parsed hParsed seed rich K outer scalar).1.1 <;> rfl

theorem fixed_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1.1.2 =
      (BinaryTerminalPhysicalAllowanceDraw.run
        frame parsed hParsed seed rich K outer scalar).1.1.2 := by
  unfold fixed
  dsimp only
  cases h : (BinaryTerminalPhysicalAllowanceDraw.run
    frame parsed hParsed seed rich K outer scalar).1.1.1.1 <;> rfl

theorem fixed_carried_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).2 =
      (BinaryTerminalPhysicalAllowanceDraw.run
        frame parsed hParsed seed rich K outer scalar).2 := by
  unfold fixed
  dsimp only
  cases h : (BinaryTerminalPhysicalAllowanceDraw.run
    frame parsed hParsed seed rich K outer scalar).1.1.1.1 <;> rfl

theorem fixed_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (fixed frame parsed hParsed seed rich K outer scalar).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalFixedLifetime.runWithTrace
            frame parsed hParsed seed rich K outer scalar).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (fixed frame parsed hParsed seed rich K outer scalar).1.2 ≤
        framePeak (BinaryTerminalPhysicalFixedLifetime.runWithTrace
          frame parsed hParsed seed rich K outer scalar).2+framePeak calculated+22 := by
  let before := BinaryTerminalPhysicalDrawLifetime.runWithTrace
    frame parsed hParsed seed rich K outer scalar
  let after := BinaryTerminalPhysicalAllowanceDraw.run
    frame parsed hParsed seed rich K outer scalar
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    parsed.1.2).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hDraw := BinaryTerminalPhysicalAllowanceDraw.run_trace_delta
    frame parsed hParsed seed rich K outer scalar
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hDraw.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.2+(framePeak calculated+20) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hDraw.2
  unfold fixed BinaryTerminalPhysicalFixedLifetime.runWithTrace
  dsimp only
  simp only [BinaryTerminalPhysicalAllowanceDraw.run_data]
  cases h : before.1.1 with
  | none =>
      let fallback := BinaryPRGGlobalFallbackLifetime.prepareWithTrace
        (resourceInput parsed.1.2.logical.request rich)
      have hw := wrap_head_delta 32 2 before.2 after.1.2 [fallback.2]
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+20) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [after.1.2,fallback.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [before.2,fallback.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 32 2 [after.1.2,fallback.2]) ≤
          framePeak (wrap 32 2 [before.2,fallback.2])+framePeak calculated+22
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
  | some row =>
      have hw := wrap_head_delta 24 2 before.2 after.1.2 []
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+20) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [before.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 24 2 [after.1.2]) ≤
          framePeak (wrap 24 2 [before.2])+framePeak calculated+22
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem fixed_fullBudget (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (value (resourceInput parsed.1.2.logical.request rich).budget : ℝ)
      (fun j => (value ((fixed frame parsed hParsed seed rich K outer scalar).1.1.1.1.read j) : ℝ)) := by
  rw [fixed_data]
  exact BinaryTerminalPhysicalFixedLifetime.accepted_fullBudget
    frame parsed hParsed seed rich K outer scalar

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  let drawn := fixed frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputLifetime.outputWithTrace
    parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  ((((output.1,drawn.1.1.1.2),drawn.1.1.2),
    wrapList parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.2]),drawn.2)

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1.1 =
      (BinaryTerminalPhysicalFramedLifetime.runWithTrace
        frame parsed hParsed seed rich K outer scalar header).1 := by
  simp only [run,BinaryTerminalPhysicalFramedLifetime.runWithTrace,fixed_data]

theorem run_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1.2 =
      (fixed frame parsed hParsed seed rich K outer scalar).1.1.2 := rfl

theorem run_carried_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).2 =
      (fixed frame parsed hParsed seed rich K outer scalar).2 := rfl

theorem run_carried_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    (run frame parsed hParsed seed rich K outer scalar header).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar header).1.1.2 =
      (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
        parsed.1 seed rich).2+calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [run_carried_work,run_allowance,fixed_carried_work,fixed_allowance]
  exact BinaryTerminalPhysicalAllowanceDraw.run_carried_total_work
    frame parsed hParsed seed rich K outer scalar

theorem run_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalFramedLifetime.runWithTrace
            frame parsed hParsed seed rich K outer scalar header).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
        framePeak (BinaryTerminalPhysicalFramedLifetime.runWithTrace
          frame parsed hParsed seed rich K outer scalar header).2+framePeak calculated+24 := by
  let before := BinaryTerminalPhysicalFixedLifetime.runWithTrace
    frame parsed hParsed seed rich K outer scalar
  let after := fixed frame parsed hParsed seed rich K outer scalar
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    parsed.1.2).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  let output := BinaryPhysicalOutputLifetime.outputWithTrace
    parsed.1.2.logical.request.prepared.original.a header.bytes before.1.1.data.toList
  have hFixed := fixed_trace_delta frame parsed hParsed seed rich K outer scalar
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hFixed.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.2+(framePeak calculated+22) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hFixed.2
  have hw := BinaryPhysicalHeapAllowanceRequest.wrapList_head_delta
    parsed.1.1 32 (parsed.1.1+2) before.2 after.1.2 [output.2]
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
    (framePeak calculated+22) hCells hFrame
  unfold run BinaryTerminalPhysicalFramedLifetime.runWithTrace
  dsimp only
  simp only [fixed_data]
  change BinaryPRGHeapPrimitiveLifetime.cells
      (wrapList parsed.1.1 32 (parsed.1.1+2) [after.1.2,output.2]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (wrapList parsed.1.1 32 (parsed.1.1+2) [before.2,output.2])+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
    framePeak (wrapList parsed.1.1 32 (parsed.1.1+2) [after.1.2,output.2]) ≤
      framePeak (wrapList parsed.1.1 32 (parsed.1.1+2) [before.2,output.2])+
        framePeak calculated+24
  exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem run_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      usage (BinaryTerminalPhysicalFramedLifetime.runWithTrace
        frame parsed hParsed seed rich K outer scalar header).2+
      usage (calculationTrace words.1 (if rich then words.1 else words.2))+56 := by
  have h := run_trace_delta frame parsed hParsed seed rich K outer scalar header
  dsimp only at h ⊢
  unfold usage
  omega

theorem accepted_read (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (suffix : List Bool) :
    BinaryRatListFrame.readRow
        ((run frame parsed hParsed seed rich K outer scalar header).1.1.1.1++suffix) =
      some (parsed.1.1,List.ofFn (fun j => value
        ((BinaryPRGWordControllerRequest.originalFixedSample seed
          parsed.1.2.logical.request rich K outer scalar).read j)),suffix) := by
  rw [run_data]
  exact BinaryTerminalPhysicalFramedLifetime.accepted_read
    frame parsed hParsed seed rich K outer scalar header suffix

theorem accepted_run_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
        BinaryTerminalPhysicalFramedLifetime.envelope frame parsed.1 seed K header.bytes.length+
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+56,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  have hRun := run_usage frame parsed hParsed seed rich K outer scalar header
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  have hOld := BinaryTerminalPhysicalFramedLifetime.accepted_usage
    frame parsed hParsed seed rich K outer scalar header
  dsimp only at hRun hCalc
  nlinarith only [hRun,hCalc,hOne,hOld]

theorem accepted_run_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1) (borrowed steps : ℕ),
      let B := BinaryTerminalPhysicalFramedLifetime.envelope
        frame parsed.1 seed K header.bytes.length+C*(frame.length+3)^d
      retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar header).1.2 steps ≤
          borrowed+B ∧
        framePeak ((run frame parsed hParsed seed rich K outer scalar header).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_run_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich K outer scalar header) borrowed steps

theorem accepted_uniform_carried_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      (run frame parsed hParsed seed rich K outer scalar header).2+
        BinaryBigEndian.littleValue
          (run frame parsed hParsed seed rich K outer scalar header).1.1.2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceCertified.accepted_uniform_carried_work
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  rw [run_carried_work,run_allowance,fixed_carried_work,fixed_allowance,
    BinaryTerminalPhysicalAllowanceDraw.run_carried_work,
    BinaryTerminalPhysicalAllowanceDraw.run_allowance]
  exact hBound frame parsed hParsed seed rich

theorem accepted_uniform_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
        C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalFramedLifetime.accepted_uniform_polynomial
  obtain ⟨P,e,hCalc⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+P+56,max d e,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let Q := frame.length+K+seed.width+seed.cap.value+header.bytes.length+3
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hBase : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have hd := Nat.pow_le_pow_right hQ (Nat.le_max_left d e)
  have he := (Nat.pow_le_pow_left hBase e).trans
    (Nat.pow_le_pow_right hQ (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) Q (by omega)
  have ho := hOld frame parsed hParsed seed rich K outer scalar header
  have hx := hCalc frame parsed hParsed rich
  have hr := run_usage frame parsed hParsed seed rich K outer scalar header
  dsimp only at hx hr
  change usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
    (C+P+56)*Q^(max d e)
  change usage (BinaryTerminalPhysicalFramedLifetime.runWithTrace
    frame parsed hParsed seed rich K outer scalar header).2 ≤ C*Q^d at ho
  nlinarith only [ho,hx,hr,hOne,Nat.mul_le_mul_left C hd,Nat.mul_le_mul_left P he]

end Blotto.BinaryTerminalPhysicalAllowanceFramed
