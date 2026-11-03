import Blotto.BinaryTerminalPhysicalAllowanceCertified
import Blotto.BinaryTerminalPhysicalDrawLifetime

/-! The terminal draw consumes the certified Boolean-allowance cache and
preserves its encoded charge. The natural charge field remains carried
cache-prefix work; terminal work is not included in that field. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceDraw
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem terminal_run_congr (seed : BinarySeedLookupTree.Store) {n : ℕ}
    {input : BinaryTerminalGrouping.Input n}
    (prepared : BinaryCachedTerminalPreparation.Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc next : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) (hn : next.value ≤ seed.cap.value) (h : pc = next) :
    BinaryWordTerminalLifetime.runWithTrace seed prepared hC hAd K outer scalar pc hp =
      BinaryWordTerminalLifetime.runWithTrace seed prepared hC hAd K outer scalar next hn := by
  subst next
  rfl

theorem logical_success (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich)
    (h : (BinaryTerminalPhysicalAllowanceCertified.run
      frame parsed hParsed seed rich).1.1.1.1 = some result) :
    (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace seed
      parsed.1.2.logical.request rich).1.1 = some result := by
  have he := congrArg Prod.fst
    (BinaryTerminalPhysicalAllowanceCertified.run_data frame parsed hParsed seed rich)
  exact BinaryTerminalPhysicalDrawLifetime.logical_success
    frame parsed hParsed seed rich result (he.symm.trans h)

theorem cursor_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (BinaryTerminalPhysicalAllowanceCertified.run
      frame parsed hParsed seed rich).1.1.1.2.value ≤ seed.cap.value := by
  have he := congrArg Prod.snd
    (BinaryTerminalPhysicalAllowanceCertified.run_data frame parsed hParsed seed rich)
  rw [he]
  exact BinaryTerminalPhysicalDrawLifetime.cursor_bound frame parsed hParsed seed rich

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ) :=
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich
  match hs : observed.1.1.1.1 with
  | none =>
      ((((none,observed.1.1.1.2),observed.1.1.2),wrap 16 2 [observed.1.2]),observed.2)
  | some result =>
      let drawn := BinaryWordTerminalLifetime.runWithTrace seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (logical_success frame parsed hParsed seed rich result hs))
        K outer scalar observed.1.1.1.2 (cursor_bound frame parsed hParsed seed rich)
      (((drawn.1,observed.1.1.2),wrap 32 2 [observed.1.2,drawn.2]),observed.2)

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.1 =
      (BinaryTerminalPhysicalDrawLifetime.runWithTrace
        frame parsed hParsed seed rich K outer scalar).1 := by
  have he := BinaryTerminalPhysicalAllowanceCertified.run_data frame parsed hParsed seed rich
  have hc := congrArg Prod.snd he
  have hs := congrArg Prod.fst he
  unfold run BinaryTerminalPhysicalDrawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    split
    · exact Prod.ext rfl hc
    · rename_i result hSome
      cases hNone.symm.trans (hs.trans hSome)
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans (hs.trans hNone)
    · rename_i other hOther
      have hx := Option.some.inj (hSome.symm.trans (hs.trans hOther))
      subst other
      exact congrArg Prod.fst (terminal_run_congr seed result.2
        (terminal_canonical parsed.1.2.logical.request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed parsed.1.2.logical.request
          rich result (logical_success frame parsed hParsed seed rich result hSome))
        K outer scalar _ _ (cursor_bound frame parsed hParsed seed rich)
        (BinaryTerminalPhysicalDrawLifetime.cursor_bound frame parsed hParsed seed rich) hc)

theorem run_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.2 =
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.1.2 := by
  unfold run
  dsimp only
  split <;> rfl

theorem run_carried_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).2 =
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2 := by
  unfold run
  dsimp only
  split <;> rfl

theorem run_carried_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    (run frame parsed hParsed seed rich K outer scalar).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar).1.1.2 =
      (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
        parsed.1 seed rich).2+calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [run_carried_work,run_allowance]
  exact BinaryTerminalPhysicalAllowanceCertified.run_carried_total_work
    frame parsed hParsed seed rich

theorem run_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalDrawLifetime.runWithTrace
            frame parsed hParsed seed rich K outer scalar).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
        framePeak (BinaryTerminalPhysicalDrawLifetime.runWithTrace
          frame parsed hParsed seed rich K outer scalar).2+framePeak calculated+20 := by
  let before := BinaryTerminalPhysicalCertifiedPrefix.runWithTrace frame parsed hParsed seed rich
  let after := BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    parsed.1.2).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hCert := BinaryTerminalPhysicalAllowanceCertified.run_trace_delta
    frame parsed hParsed seed rich
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hCert.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.2+(framePeak calculated+18) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hCert.2
  have he := BinaryTerminalPhysicalAllowanceCertified.run_data frame parsed hParsed seed rich
  have hc := congrArg Prod.snd he
  have hs := congrArg Prod.fst he
  unfold run BinaryTerminalPhysicalDrawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    split
    · have hw := wrap_head_delta 16 2 before.2 after.1.2 []
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+18) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [before.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 16 2 [after.1.2]) ≤
          framePeak (wrap 16 2 [before.2])+framePeak calculated+20
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
    · rename_i result hSome
      cases hNone.symm.trans (hs.trans hSome)
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans (hs.trans hNone)
    · rename_i other hOther
      have hx := Option.some.inj (hSome.symm.trans (hs.trans hOther))
      subst other
      have ht := terminal_run_congr seed result.2
        (terminal_canonical parsed.1.2.logical.request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed parsed.1.2.logical.request
          rich result (logical_success frame parsed hParsed seed rich result hSome))
        K outer scalar _ _ (cursor_bound frame parsed hParsed seed rich)
        (BinaryTerminalPhysicalDrawLifetime.cursor_bound frame parsed hParsed seed rich) hc
      have hTrace := congrArg Prod.snd ht
      rw [hTrace]
      let terminal := BinaryWordTerminalLifetime.runWithTrace seed result.2
        (terminal_canonical parsed.1.2.logical.request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed parsed.1.2.logical.request
          rich result (logical_success frame parsed hParsed seed rich result hSome))
        K outer scalar before.1.2
        (BinaryTerminalPhysicalDrawLifetime.cursor_bound frame parsed hParsed seed rich)
      have hw := wrap_head_delta 32 2 before.2 after.1.2 [terminal.2]
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+18) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [after.1.2,terminal.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [before.2,terminal.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 32 2 [after.1.2,terminal.2]) ≤
          framePeak (wrap 32 2 [before.2,terminal.2])+framePeak calculated+20
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem run_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
      usage (BinaryTerminalPhysicalDrawLifetime.runWithTrace
        frame parsed hParsed seed rich K outer scalar).2+
      usage (calculationTrace words.1 (if rich then words.1 else words.2))+52 := by
  have h := run_trace_delta frame parsed hParsed seed rich K outer scalar
  dsimp only at h ⊢
  unfold usage
  omega

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.1 =
      BinaryPRGWordControllerRequest.run seed parsed.1.2.logical.request rich K outer scalar := by
  rw [run_data]
  exact BinaryTerminalPhysicalDrawLifetime.accepted_erasure
    frame parsed hParsed seed rich K outer scalar

theorem accepted_run_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K),
      usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
        BinaryTerminalPhysicalDrawLifetime.envelope frame parsed.1 seed K+
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+52,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar
  have hRun := run_usage frame parsed hParsed seed rich K outer scalar
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  have hOld := BinaryTerminalPhysicalDrawLifetime.accepted_usage
    frame parsed hParsed seed rich K outer scalar
  dsimp only at hRun hCalc
  nlinarith only [hRun,hCalc,hOne,hOld]

theorem accepted_run_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ),
      let B := BinaryTerminalPhysicalDrawLifetime.envelope frame parsed.1 seed K+
        C*(frame.length+3)^d
      retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar).1.2 steps ≤
          borrowed+B ∧
        framePeak ((run frame parsed hParsed seed rich K outer scalar).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_run_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich K outer scalar) borrowed steps

end Blotto.BinaryTerminalPhysicalAllowanceDraw
