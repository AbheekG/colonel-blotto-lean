import Blotto.BinaryWrapperEmission
import Blotto.BinaryTerminalPhysicalAllowanceCache
import Blotto.BinaryTerminalPhysicalCertifiedPrefix

/-! Certification of the cache produced by the Boolean-allowance route.
The charge field carries cache-prefix work only; it is not a claim that later
terminal execution has been priced. The certificate is attached to the
returned cache without preparing that cache again. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceCertified
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryTerminalCacheCertificate
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cache_correct (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich)
    (h : (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).1.1.1.1 =
      some result) :
    result.2 = BinaryTerminalCacheLifetime.erase (BinaryCachedTerminalPreparation.prepare
      (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich result.1)) := by
  have hOld : (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTrace
      parsed.1 seed rich).1.1 = some result := by
    change (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
      parsed.1 seed rich).1.1.1 = some result
    rw [← BinaryTerminalPhysicalAllowanceCache.run_data]
    exact h
  exact BinaryTerminalPhysicalCertifiedPrefix.accepted_cache_correct
    frame parsed hParsed seed rich result hOld

def runReference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  let observed := BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich
  match hs : observed.1.1.1.1 with
  | none =>
      ((((none,observed.1.1.1.2),observed.1.1.2),wrap 16 2 [observed.1.2]),observed.2)
  | some result =>
      let certified := certifyWithTrace result.2
        (cache_correct frame parsed hParsed seed rich result hs)
      ((((some ⟨result.1,certified.1⟩,observed.1.1.1.2),observed.1.1.2),
        wrap 24 2 [observed.1.2,certified.2]),observed.2)

def runWithCharges (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    ((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges :=
  let returned := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
  let observed := returned.1
  match hs : observed.1.1.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
      (((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  | some result =>
      let certified := certifyWithTrace result.2
        (cache_correct frame parsed hParsed seed rich result hs)
      let emitted := BinaryWrapperEmission.two 24 2 observed.1.2 certified.2
      (((((some ⟨result.1,certified.1⟩,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  (runWithCharges frame parsed hParsed seed rich).1

theorem run_eq_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    run frame parsed hParsed seed rich = runReference frame parsed hParsed seed rich := by
  unfold run runWithCharges runReference
  simp only [BinaryTerminalPhysicalAllowanceCache.run]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace]

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (run frame parsed hParsed seed rich).1.1.1 =
      (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed seed rich).1 := by
  have he := BinaryTerminalPhysicalAllowanceCache.run_data parsed.1 seed rich
  have hc := congrArg Prod.snd he
  have hs := congrArg Prod.fst he
  rw [run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
  dsimp only
  split
  · rename_i hNone
    split
    · exact Prod.ext rfl hc
    · rename_i result hSome
      have hx := hNone.symm.trans (hs.trans hSome)
      cases hx
  · rename_i result hSome
    split
    · rename_i hNone
      have hx := hSome.symm.trans (hs.trans hNone)
      cases hx
    · rename_i other hOther
      have hx := Option.some.inj (hSome.symm.trans (hs.trans hOther))
      subst other
      exact Prod.ext rfl hc

theorem run_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (run frame parsed hParsed seed rich).1.1.2 =
      (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).1.1.2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split <;> rfl

theorem run_carried_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (run frame parsed hParsed seed rich).2 =
      (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split <;> rfl

theorem run_carried_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    (run frame parsed hParsed seed rich).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich).1.1.2 =
      (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
        parsed.1 seed rich).2+calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [run_carried_work,run_allowance]
  exact BinaryTerminalPhysicalAllowanceCache.run_total_work parsed.1 seed rich

theorem run_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (run frame parsed hParsed seed rich).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
            frame parsed hParsed seed rich).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (run frame parsed hParsed seed rich).1.2 ≤
        framePeak (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
          frame parsed hParsed seed rich).2+framePeak calculated+18 := by
  let before := BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
    parsed.1 seed rich
  let after := BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    parsed.1.2).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hCache := BinaryTerminalPhysicalAllowanceCache.run_trace_delta parsed.1 seed rich
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.1.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hCache.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.1.2+(framePeak calculated+16) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hCache.2
  have hs := congrArg Prod.fst
    (BinaryTerminalPhysicalAllowanceCache.run_data parsed.1 seed rich)
  rw [run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
  dsimp only
  split
  · rename_i hNone
    split
    · have hw := wrap_head_delta 16 2 before.1.2 after.1.2 []
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+16) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [before.1.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 16 2 [after.1.2]) ≤
          framePeak (wrap 16 2 [before.1.2])+framePeak calculated+18
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
    · rename_i result hSome
      have hx := hNone.symm.trans (hs.trans hSome)
      cases hx
  · rename_i result hSome
    split
    · rename_i hNone
      have hx := hSome.symm.trans (hs.trans hNone)
      cases hx
    · have hw := wrap_head_delta 24 2 before.1.2 after.1.2 [wrap 64 2 []]
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+16) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [after.1.2,wrap 64 2 []]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [before.1.2,wrap 64 2 []])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 24 2 [after.1.2,wrap 64 2 []]) ≤
          framePeak (wrap 24 2 [before.1.2,wrap 64 2 []])+framePeak calculated+18
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem run_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])
    usage (run frame parsed hParsed seed rich).1.2 ≤
      usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed seed rich).2+
      usage (calculationTrace words.1 (if rich then words.1 else words.2))+50 := by
  have h := run_trace_delta frame parsed hParsed seed rich
  dsimp only at h ⊢
  unfold usage
  omega

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (run frame parsed hParsed seed rich).1.1.1 =
      BinaryPRGHeapCertifiedPrefixLifetime.reference seed parsed.1.2.logical.request rich := by
  rw [run_data]
  exact BinaryTerminalPhysicalCertifiedPrefix.accepted_reference frame parsed hParsed seed rich

theorem accepted_run_usage_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run frame parsed hParsed seed rich).1.2 ≤
        usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
          frame parsed hParsed seed rich).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+50,d,?_⟩
  intro frame parsed hParsed seed rich
  have hRun := run_usage frame parsed hParsed seed rich
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  dsimp only at hRun hCalc
  nlinarith only [hRun,hCalc,hOne]

theorem accepted_run_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run frame parsed hParsed seed rich).1.2 ≤
        BinaryTerminalPhysicalCertifiedPrefix.envelope frame parsed.1 seed+
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hExtra⟩ := accepted_run_usage_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  have he := hExtra frame parsed hParsed seed rich
  have ho := BinaryTerminalPhysicalCertifiedPrefix.accepted_usage
    frame parsed hParsed seed rich
  omega

theorem accepted_run_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ),
      let B := BinaryTerminalPhysicalCertifiedPrefix.envelope frame parsed.1 seed+
        C*(frame.length+3)^d
      retainedHeap borrowed (run frame parsed hParsed seed rich).1.2 steps ≤ borrowed+B ∧
        framePeak ((run frame parsed hParsed seed rich).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_run_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich) borrowed steps

theorem accepted_uniform_carried_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (run frame parsed hParsed seed rich).2+
        BinaryBigEndian.littleValue (run frame parsed hParsed seed rich).1.1.2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceCache.accepted_uniform_work
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  rw [run_carried_work,run_allowance]
  exact hBound frame parsed hParsed seed rich

theorem accepted_uniform_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run frame parsed hParsed seed rich).1.2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalCertifiedPrefix.accepted_uniform_polynomial
  obtain ⟨P,e,hExtra⟩ := accepted_run_usage_overhead
  refine ⟨C+P,max d e,?_⟩
  intro frame parsed hParsed seed rich
  let Q := frame.length+seed.width+seed.cap.value+3
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hBase : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have hd := Nat.pow_le_pow_right hQ (Nat.le_max_left d e)
  have he := (Nat.pow_le_pow_left hBase e).trans
    (Nat.pow_le_pow_right hQ (Nat.le_max_right d e))
  have ho := hOld frame parsed hParsed seed rich
  have hx := hExtra frame parsed hParsed seed rich
  change usage (run frame parsed hParsed seed rich).1.2 ≤ (C+P)*Q^(max d e)
  change usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
    frame parsed hParsed seed rich).2 ≤ C*Q^d at ho
  nlinarith only [ho,hx,Nat.mul_le_mul_left C hd,Nat.mul_le_mul_left P he]

theorem runWithCharges_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runWithCharges frame parsed hParsed seed rich).1 = run frame parsed hParsed seed rich := rfl

theorem runWithCharges_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let child := (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich).2
    let charges := (runWithCharges frame parsed hParsed seed rich).2
    charges.primitive = child.primitive ∧ charges.coinSource = child.coinSource ∧
      charges.write = child.write ∧ charges.native = child.native := by
  unfold runWithCharges
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_step (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let child := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
    let produced := runWithCharges frame parsed hParsed seed rich
    BinaryExecutionCharges.total produced.2 ≤ BinaryExecutionCharges.total child.2+
        5*produced.1.1.2.length+8 ∧
      child.1.1.2.length ≤ produced.1.1.2.length ∧ child.1.2 ≤ produced.1.2 := by
  unfold runWithCharges
  dsimp only
  split <;> simp only [BinaryExecutionCharges.total_addWrapper,BinaryWrapperEmission.one_work,
    BinaryWrapperEmission.two_work,BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length] <;> omega

end Blotto.BinaryTerminalPhysicalAllowanceCertified
