import Blotto.BinaryPhysicalHeapAllowanceRequest
import Blotto.BinaryTerminalPhysicalRouteLifetime

/-! The physical terminal cache consumes the request carrying a Boolean
builder allowance. It retains that word and the calculator work/trace;
the numerical allowance interpretation occurs only in specification lemmas.
The actual request charges are retained as separate fields, and each reached
cache outcome adds its own returned wrapper-emission cost. The complete
preceding value/trace/source-work record remains exact. Local cache trace
construction and full native prices remain separate obligations. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceCache
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial
open BinaryTerminalPhysicalRouteLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000

abbrev PhysicalRequest := Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n
abbrev Parsed := PhysicalRequest × List Bool

def runReference (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  let resource := BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich
  match resource.1.1.1.1 with
  | none =>
      ((((none,resource.1.1.1.2),resource.1.1.2),wrap 16 2 [resource.1.2]),resource.2+4)
  | some state =>
      let cached := cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state)
        parsed.2.physical.lengthStore
      ((((some ⟨state,cached.1.1⟩,resource.1.1.1.2),resource.1.1.2),
        wrap 24 2 [resource.1.2,cached.1.2]),resource.2+cached.2+8)

def runWithCharges (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    ((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges :=
  let returned := BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.2 rich
  let resource := returned.1
  match resource.1.1.1.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 resource.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((none,resource.1.1.1.2),resource.1.1.2),emitted.1.1),resource.2+4),
        BinaryExecutionCharges.addWrapper returned.2 (emitted.1.2+emitted.2))
  | some state =>
      let cached := cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state)
        parsed.2.physical.lengthStore
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 resource.1.2) (.shifted 2 cached.1.2))
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((some ⟨state,cached.1.1⟩,resource.1.1.1.2),resource.1.1.2),
        emitted.1.1),resource.2+cached.2+8),
        BinaryExecutionCharges.addWrapper returned.2 (emitted.1.2+emitted.2))

def run (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  (runWithCharges parsed seed rich).1

theorem run_eq_reference (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    run parsed seed rich = runReference parsed seed rich := by
  unfold run runWithCharges runReference
  simp only [BinaryPhysicalHeapAllowanceRequest.run]
  split <;> simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_data,
    BinaryTracePlanMeasured.denote,List.append_nil,wrap,combine]

theorem run_data (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store)
    (rich : Bool) :
    (run parsed seed rich).1.1.1 =
      (runCachedPrefixWithTraceAndWork parsed seed rich).1.1 := by
  rw [run_eq_reference]
  unfold runReference runCachedPrefixWithTraceAndWork
  dsimp only
  simp only [BinaryPhysicalHeapAllowanceRequest.run_data]
  cases h : (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    seed parsed.2 rich).1.1.1 <;> rfl

theorem run_allowance (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store)
    (rich : Bool) :
    (run parsed seed rich).1.1.2 =
      (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.1.2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  cases h : (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.1.1.1 <;> rfl

theorem run_total_work (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store)
    (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.2).1.1.getD ([],[])
    (run parsed seed rich).2+BinaryBigEndian.littleValue (run parsed seed rich).1.1.2 =
      (runCachedPrefixWithTraceAndWork parsed seed rich).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [run_allowance]
  have hResource := BinaryPhysicalHeapAllowanceRequest.run_total_work seed parsed.2 rich
  rw [run_eq_reference]
  unfold runReference runCachedPrefixWithTraceAndWork
  dsimp only
  simp only [BinaryPhysicalHeapAllowanceRequest.run_data]
  cases h : (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    seed parsed.2 rich).1.1.1 <;> dsimp only <;> omega

theorem run_trace_delta (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store)
    (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.2).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (run parsed seed rich).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (runCachedPrefixWithTraceAndWork parsed seed rich).1.2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (run parsed seed rich).1.2 ≤
        framePeak (runCachedPrefixWithTraceAndWork parsed seed rich).1.2+
          framePeak calculated+16 := by
  let before := BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    seed parsed.2 rich
  let after := BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    parsed.2).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hResource := BinaryPhysicalHeapAllowanceRequest.run_trace_delta seed parsed.2 rich
  rw [BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork_erases,
    ← BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_erases]
    at hResource
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.1.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hResource.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.1.2+(framePeak calculated+14) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hResource.2
  rw [run_eq_reference]
  unfold runReference runCachedPrefixWithTraceAndWork
  dsimp only
  simp only [BinaryPhysicalHeapAllowanceRequest.run_data]
  cases h : before.1.1.1 with
  | none =>
      have hw := wrap_head_delta 16 2 before.1.2 after.1.2 []
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+14) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [before.1.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 16 2 [after.1.2]) ≤
          framePeak (wrap 16 2 [before.1.2])+framePeak calculated+16
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
  | some state =>
      let cached := cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state)
        parsed.2.physical.lengthStore
      have hw := wrap_head_delta 24 2 before.1.2 after.1.2 [cached.1.2]
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+14) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [after.1.2,cached.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [before.1.2,cached.1.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 24 2 [after.1.2,cached.1.2]) ≤
          framePeak (wrap 24 2 [before.1.2,cached.1.2])+framePeak calculated+16
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem run_usage (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store)
    (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.2).1.1.getD ([],[])
    usage (run parsed seed rich).1.2 ≤
      usage (runCachedPrefixWithTraceAndWork parsed seed rich).1.2+
        usage (calculationTrace words.1 (if rich then words.1 else words.2))+48 := by
  have h := run_trace_delta parsed seed rich
  dsimp only at h ⊢
  unfold usage
  omega

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (run parsed.1 seed rich).1.1.1 =
      BinaryPRGHeapCachedPrefixLifetime.reference seed parsed.1.2.logical.request rich := by
  rw [run_data]
  exact accepted_cached_prefix_reference frame parsed hParsed seed rich

theorem accepted_run_work_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (run parsed.1 seed rich).2+
        BinaryBigEndian.littleValue (run parsed.1 seed rich).1.1.2 ≤
        (runCachedPrefixWithTraceAndWork parsed.1 seed rich).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPhysicalBuildAllowance.accepted_readback_calculation_work_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  rw [run_total_work]
  exact Nat.add_le_add_left (hBound frame parsed hParsed rich) _

theorem accepted_run_usage_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run parsed.1 seed rich).1.2 ≤
        usage (runCachedPrefixWithTraceAndWork parsed.1 seed rich).1.2+
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+48,d,?_⟩
  intro frame parsed hParsed seed rich
  have hRun := run_usage parsed.1 seed rich
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  dsimp only at hRun hCalc
  nlinarith only [hRun,hCalc,hOne]

theorem accepted_run_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run parsed.1 seed rich).1.2 ≤
        cachedPrefixEnvelope frame parsed.1 seed+C*(frame.length+3)^d := by
  obtain ⟨C,d,hExtra⟩ := accepted_run_usage_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  have he := hExtra frame parsed hParsed seed rich
  have ho := accepted_cached_prefix_usage frame parsed hParsed seed rich
  change usage (runCachedPrefixWithTraceAndWork parsed.1 seed rich).1.2 ≤ _ at ho
  omega

theorem accepted_run_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ),
      let B := cachedPrefixEnvelope frame parsed.1 seed+C*(frame.length+3)^d
      retainedHeap borrowed (run parsed.1 seed rich).1.2 steps ≤ borrowed+B ∧
        framePeak ((run parsed.1 seed rich).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_run_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich) borrowed steps

theorem accepted_uniform_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (run parsed.1 seed rich).2+
        BinaryBigEndian.littleValue (run parsed.1 seed rich).1.1.2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := accepted_cached_prefix_uniform_work
  obtain ⟨P,e,hExtra⟩ := accepted_run_work_overhead
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
  change (run parsed.1 seed rich).2+
    BinaryBigEndian.littleValue (run parsed.1 seed rich).1.1.2 ≤ (C+P)*Q^(max d e)
  change (runCachedPrefixWithTraceAndWork parsed.1 seed rich).2 ≤ C*Q^d at ho
  nlinarith only [ho,hx,Nat.mul_le_mul_left C hd,Nat.mul_le_mul_left P he]

theorem accepted_uniform_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run parsed.1 seed rich).1.2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := accepted_cached_prefix_uniform_polynomial
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
  change usage (run parsed.1 seed rich).1.2 ≤ (C+P)*Q^(max d e)
  change usage (runCachedPrefixWithTraceAndWork parsed.1 seed rich).1.2 ≤ C*Q^d at ho
  nlinarith only [ho,hx,Nat.mul_le_mul_left C hd,Nat.mul_le_mul_left P he]

theorem runWithCharges_compat (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runWithCharges parsed seed rich).1 = run parsed seed rich := rfl

theorem request_work_le_run (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).2 ≤ (run parsed seed rich).2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split <;> dsimp only <;> omega

theorem runWithCharges_fields (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let child := (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.2 rich).2
    let charges := (runWithCharges parsed seed rich).2
    charges.primitive = child.primitive ∧ charges.coinSource = child.coinSource ∧
      charges.write = child.write ∧ charges.native = child.native := by
  unfold runWithCharges
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_total_bound (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (B : ℕ) (hCache : ∀ state,
      (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.1.1.1 = some state →
      (cacheWithTraceAndWork (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state)
        parsed.2.physical.lengthStore).1.2.length ≤ B) :
    BinaryExecutionCharges.total (runWithCharges parsed seed rich).2 ≤
      BinaryExecutionCharges.total (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.2 rich).2+
        5*(BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.2.length+5*B+35 := by
  unfold runWithCharges
  dsimp only
  split
  · dsimp only
    simp only [BinaryExecutionCharges.total_addWrapper]
    have h := BinaryTracePlanMeasured.emitFull_total
      (.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.2)) []
      ((BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.2.length+5) (by
        simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
        omega)
    simp only [BinaryPhysicalHeapAllowanceRequest.run] at h ⊢
    omega
  · rename_i state hState
    dsimp only
    simp only [BinaryExecutionCharges.total_addWrapper]
    let cached := cacheWithTraceAndWork
      (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore
    have hc := hCache state hState
    change cached.1.2.length ≤ B at hc
    have h := BinaryTracePlanMeasured.emitFull_total
      (.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.2)
          (.shifted 2 cached.1.2))) []
      ((BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.2.length+cached.1.2.length+7) (by
        simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
        omega)
    simp only [cached,BinaryPhysicalHeapAllowanceRequest.run] at h hc ⊢
    omega

end Blotto.BinaryTerminalPhysicalAllowanceCache
