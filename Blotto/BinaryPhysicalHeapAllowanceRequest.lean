import Blotto.BinaryPhysicalHeapAllowanceInitial
import Blotto.BinaryHeapMaterializationMeasured
import Blotto.BinaryHeapMaterializationPlan
import Blotto.BinaryExecutionCharges

/-! The traced Boolean builder allowance survives terminal materialization and
the complete physical resource-request wrappers. Its numerical interpretation
is a proof observer; the producer carries the bit word without decoding it.
The selected nativeAt helper also forwards the actual source guard/step/etc.
extra and coin/source emission ledger on both exhaustion and terminal paths.
Its preceding result/trace/source record remains exact. Actual materialization
and the reached native wrapper now share a final plan emission, whose returned
charge is retained separately. Complete native scalar/header/reference/allocator
prices and later certified/draw/raw/pair transport remain separate obligations. -/

namespace Blotto.BinaryPhysicalHeapAllowanceRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPhysicalHeapAllowanceInitial
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {n : ℕ}

def nativeAtReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let drawn := sourceAt seed request rich pc hp
  match drawn.1.1.1.2.1 with
  | none =>
      ((((none,drawn.1.1.1.2.2),drawn.1.1.2),wrap 16 2 [drawn.1.2]),drawn.2+2)
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state
      let terminalWork := (BinaryPRGHeapResourceMaterialization.materializeWithWork
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state).2
      ((((some terminal.1,drawn.1.1.1.2.2),drawn.1.1.2),
        wrap 24 2 [drawn.1.2,terminal.2]),drawn.2+terminalWork+4)

/- The selected request consumes one measured materialization. The former
traced/value plus work replay above is retained only as a proof reference. -/
def nativeAtSourceReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let drawn := sourceAt seed request rich pc hp
  match drawn.1.1.1.2.1 with
  | none => ((((none,drawn.1.1.1.2.2),drawn.1.1.2),wrap 16 2 [drawn.1.2]),drawn.2+2)
  | some state =>
      let terminal := BinaryHeapMaterializationMeasured.materialize selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state
      ((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        wrap 24 2 [drawn.1.2,terminal.1.2]),drawn.2+terminal.2+4)


def nativeAtMeasuredReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × (ℕ × ℕ)) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let produced := sourceAtTraceMeasured seed request rich pc hp
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      (((((none,drawn.1.1.1.2.2),drawn.1.1.2),wrap 16 2 [drawn.1.2]),drawn.2+2),
        (produced.1.2,produced.2))
  | some state =>
      let terminal := BinaryHeapMaterializationMeasured.materialize selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state
      (((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        wrap 24 2 [drawn.1.2,terminal.1.2]),drawn.2+terminal.2+4),
          (produced.1.2,produced.2))


def nativeAtWithWritesReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × (ℕ × ℕ))) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let returned := sourceAtTraceWithWrites seed request rich pc hp
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      ((((((none,drawn.1.1.1.2.2),drawn.1.1.2),wrap 16 2 [drawn.1.2]),drawn.2+2),
        (produced.1.2,produced.2)),returned.2)
  | some state =>
      let terminal := BinaryHeapMaterializationMeasured.materialize selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state
      ((((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        wrap 24 2 [drawn.1.2,terminal.1.2]),drawn.2+terminal.2+4),
          (produced.1.2,produced.2)),returned.2)

/-- Materialization remains a plan until the reached native wrapper emits it.
The complete preceding record is returned as the first projection. -/
def nativeAtWithEmission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × (ℕ × ℕ))) × ℕ) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let returned := sourceAtTraceWithWrites seed request rich pc hp
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 drawn.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((((none,drawn.1.1.1.2.2),drawn.1.1.2),emitted.1.1),drawn.2+2),
        (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2)
  | some state =>
      let terminal := BinaryHeapMaterializationPlan.materializeAt selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (sourceAt_cap seed request rich pc hp) state 2
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 drawn.1.2) terminal.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        emitted.1.1),drawn.2+terminal.2+4),
          (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2)

theorem nativeAtWithEmission_refines (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).1 = nativeAtWithWritesReference seed request rich pc hp := by
  unfold nativeAtWithEmission nativeAtWithWritesReference
  dsimp only
  split
  · simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_data,
      BinaryTracePlanMeasured.denote,List.append_nil,wrap,combine]
  · rename_i state hState
    have h := BinaryHeapMaterializationPlan.materializeAt_refines
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length)
      (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1
      (sourceAt_cap seed request rich pc hp) state 2
    simp only [BinaryHeapEnumerationPlan.view,BinaryHeapEnumerationPlan.offset] at h
    have hv := congrArg (fun out => out.1.1) h
    have ht := congrArg (fun out => out.1.2) h
    have hw := congrArg (fun out => out.2) h
    dsimp only at hv ht hw
    simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_data,
      BinaryTracePlanMeasured.denote,List.append_nil,hv,ht,hw,wrap,combine]

def nativeAtWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × (ℕ × ℕ))) × ℕ :=
  (nativeAtWithEmission seed request rich pc hp).1

theorem nativeAtWithWrites_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeAtWithWrites seed request rich pc hp = nativeAtWithWritesReference seed request rich pc hp :=
  nativeAtWithEmission_refines seed request rich pc hp

def nativeAtMeasured (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × (ℕ × ℕ)) :=
  (nativeAtWithWrites seed request rich pc hp).1

theorem nativeAtMeasured_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeAtMeasured seed request rich pc hp = nativeAtMeasuredReference seed request rich pc hp := by
  unfold nativeAtMeasured
  rw [nativeAtWithWrites_eq_reference]
  unfold nativeAtWithWritesReference nativeAtMeasuredReference
  dsimp only
  simp only [sourceAtTraceWithWrites_compat]
  split <;> rfl

def nativeAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) :=
  (nativeAtMeasured seed request rich pc hp).1

theorem nativeAt_eq_source_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeAt seed request rich pc hp = nativeAtSourceReference seed request rich pc hp := by
  unfold nativeAt
  rw [nativeAtMeasured_eq_reference]
  unfold nativeAtMeasuredReference nativeAtSourceReference
  dsimp only
  simp only [sourceAtTraceMeasured_source]
  split <;> rfl


theorem nativeAt_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeAt seed request rich pc hp = nativeAtReference seed request rich pc hp := by
  rw [nativeAt_eq_source_reference]
  unfold nativeAtSourceReference nativeAtReference
  dsimp only
  split
  · rfl
  · simp only [BinaryHeapMaterializationMeasured.materialize_erases,BinaryHeapMaterializationMeasured.materialize_work]

theorem nativeAt_data (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAt seed request rich pc hp).1.1.1 =
      (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
        seed request rich pc hp).1.1 := by
  rw [nativeAt_eq_reference]
  unfold nativeAtReference BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAt_data]
  cases h : (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
    seed request rich pc hp).1.1.2.1 <;> rfl

theorem nativeAt_allowance (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAt seed request rich pc hp).1.1.2 =
      (sourceAt seed request rich pc hp).1.1.2 := by
  rw [nativeAt_eq_reference]
  unfold nativeAtReference
  dsimp only
  cases h : (sourceAt seed request rich pc hp).1.1.1.2.1 <;> rfl

theorem nativeAt_work (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (nativeAt seed request rich pc hp).2 =
      (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
        seed request rich pc hp).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  have hSource := sourceAt_work seed request rich pc hp
  rw [nativeAt_eq_reference]
  unfold nativeAtReference BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAt_data]
  cases h : (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
      seed request rich pc hp).1.1.2.1 <;> dsimp only <;> omega

theorem nativeAt_total_work (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (nativeAt seed request rich pc hp).2+
      BinaryBigEndian.littleValue (nativeAt seed request rich pc hp).1.1.2 =
      (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndBuildWork
        seed request rich pc hp).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [nativeAt_work,nativeAt_allowance,sourceAt_allowance_value,
    BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndBuildWork_charge]
  omega

theorem nativeAt_trace_delta (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (nativeAt seed request rich pc hp).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
            seed request rich pc hp).1.2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (nativeAt seed request rich pc hp).1.2 ≤
        framePeak (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
          seed request rich pc hp).1.2+framePeak calculated+10 := by
  let before := BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
    seed request rich pc hp
  let after := sourceAt seed request rich pc hp
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hSource := sourceAt_trace_delta seed request rich pc hp
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.1.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hSource.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.1.2+(framePeak calculated+8) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hSource.2
  rw [nativeAt_eq_reference]
  unfold nativeAtReference BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAt_data]
  cases h : before.1.1.2.1 with
  | none =>
      have hw := wrap_head_delta 16 2 before.1.2 after.1.2 []
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+8) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [before.1.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 16 2 [after.1.2]) ≤
          framePeak (wrap 16 2 [before.1.2])+framePeak calculated+10
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable
          (BinaryPRGResourceWork.resourceInput request.logical.request rich).length)
        before.1.1.1 (BinaryPhysicalHeapRequestLifetime.sourceAt_cap seed request rich pc hp) state
      have hw := wrap_head_delta 24 2 before.1.2 after.1.2 [terminal.2]
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
        (framePeak calculated+8) hCells hFrame
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [after.1.2,terminal.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [before.1.2,terminal.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
        framePeak (wrap 24 2 [after.1.2,terminal.2]) ≤
          framePeak (wrap 24 2 [before.1.2,terminal.2])+framePeak calculated+10
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

def runReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) :=
  let drawn := nativeAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  ((drawn.1.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2)
    [wrap 24 2 [drawn.1.2]]),drawn.2+
      BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      BinaryPhysicalHeapRequestLifetime.preparationResidualAllowance request)

def runWithCharges (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    ((((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) :=
  let returned := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let drawn := returned.1.1.1
  let width := seed.cap.bits.length
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation width,.frames (width+2),.arrayAllocation 16,.frames 4,.arrayAllocation 24])
    (.shifted 4 drawn.1.2)
  let emitted := BinaryTracePlanMeasured.emitFull plan []
  (((drawn.1.1,emitted.1.1),drawn.2+
      BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      BinaryPhysicalHeapRequestLifetime.preparationResidualAllowance request),
    ⟨returned.1.1.2.1,returned.1.1.2.2,returned.1.2,returned.2,emitted.1.2+emitted.2⟩)

def run (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (((BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length ×
      List Bool) × Trace) × ℕ) :=
  (runWithCharges seed request rich).1

theorem run_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    run seed request rich = runReference seed request rich := by
  simp only [run,runWithCharges,runReference,nativeAt,nativeAtMeasured,nativeAtWithWrites,
    BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_data,
    BinaryTracePlanMeasured.denote,List.append_nil,wrapList,wrap,combine,
    BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose]
  rfl

theorem run_data (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (run seed request rich).1.1.1 =
      (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
        seed request rich).1.1 := by
  let pc := BinaryWordIndexCoinController.zeroIndex seed
  have hp : pc.value ≤ seed.cap.value := by
    rw [BinaryWordIndexCoinController.zeroIndex_value]; omega
  rw [run_eq_reference]
  change (nativeAt seed request rich pc hp).1.1.1 =
    (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndBuildWork
      seed request rich pc hp).1.1
  rw [nativeAt_data]
  exact (congrArg Prod.fst
    (BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndBuildWork_erases
      seed request rich pc hp)).symm

theorem run_allowance (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (run seed request rich).1.1.2 =
      (sourceAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).1.1.2 := by
  rw [run_eq_reference]
  exact nativeAt_allowance seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)

theorem run_total_work (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (run seed request rich).2+
      BinaryBigEndian.littleValue (run seed request rich).1.1.2 =
      (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
        seed request rich).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  have hNative := nativeAt_total_work seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  rw [run_eq_reference]
  unfold runReference BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    BinaryPhysicalHeapRequestLifetime.runWithTraceAndBuildWork
    BinaryPhysicalHeapRequestLifetime.runAtWithTraceAndBuildWork
  dsimp only
  omega

theorem wrapList_head_delta (list slots frames : ℕ) (before after : Trace)
    (rest : List Trace) (A F : ℕ)
    (hCells : BinaryPRGHeapPrimitiveLifetime.cells after ≤
      BinaryPRGHeapPrimitiveLifetime.cells before+A)
    (hFrame : framePeak after ≤ framePeak before+F) :
    BinaryPRGHeapPrimitiveLifetime.cells (wrapList list slots frames (after :: rest)) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrapList list slots frames (before :: rest))+A ∧
      framePeak (wrapList list slots frames (after :: rest)) ≤
        framePeak (wrapList list slots frames (before :: rest))+F+2 := by
  have hNew := framePeak_under 2 after
  have hOld := framePeak_le_under 2 before
  simp only [wrapList,wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold BinaryPRGHeapPrimitiveLifetime.cells at hCells
  exact ⟨by omega,by omega⟩

theorem run_trace_delta (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (run seed request rich).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork
            seed request rich).1.2+32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (run seed request rich).1.2 ≤
        framePeak (BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork
          seed request rich).1.2+framePeak calculated+14 := by
  let pc := BinaryWordIndexCoinController.zeroIndex seed
  have hp : pc.value ≤ seed.cap.value := by
    rw [BinaryWordIndexCoinController.zeroIndex_value]; omega
  let before := BinaryPhysicalHeapRequestLifetime.nativeAtWithTraceAndWork
    seed request rich pc hp
  let after := nativeAt seed request rich pc hp
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  have hNative := nativeAt_trace_delta seed request rich pc hp
  have hCells : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.1.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hNative.1
  have hFrame : framePeak after.1.2 ≤ framePeak before.1.2+(framePeak calculated+10) := by
    simpa only [before,after,words,calculated,Nat.add_assoc] using hNative.2
  have hAt := wrap_head_delta 24 2 before.1.2 after.1.2 []
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
    (framePeak calculated+10) hCells hFrame
  have hTop := wrapList_head_delta seed.cap.bits.length 16 (seed.cap.bits.length+2)
    (wrap 24 2 [before.1.2]) (wrap 24 2 [after.1.2]) []
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
    (framePeak calculated+10+2) hAt.1 hAt.2
  rw [run_eq_reference]
  change BinaryPRGHeapPrimitiveLifetime.cells
      (wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2)
        [wrap 24 2 [after.1.2]]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2)
            [wrap 24 2 [before.1.2]])+32+
          BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
    framePeak (wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2)
      [wrap 24 2 [after.1.2]]) ≤
      framePeak (wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2)
        [wrap 24 2 [before.1.2]])+framePeak calculated+14
  exact ⟨hTop.1.trans_eq (by omega),hTop.2.trans_eq (by omega)⟩

theorem run_usage (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    usage (run seed request rich).1.2 ≤
      usage (BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork
        seed request rich).1.2+
      usage (calculationTrace words.1 (if rich then words.1 else words.2))+46 := by
  have h := run_trace_delta seed request rich
  dsimp only at h ⊢
  unfold usage
  omega

theorem accepted_run_work_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (run seed parsed.1.2 rich).2+
        BinaryBigEndian.littleValue (run seed parsed.1.2 rich).1.1.2 ≤
        (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
          seed parsed.1.2 rich).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPhysicalBuildAllowance.accepted_readback_calculation_work_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  rw [run_total_work]
  exact Nat.add_le_add_left (hBound frame parsed hParsed rich) _

theorem accepted_run_usage_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run seed parsed.1.2 rich).1.2 ≤
        usage (BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork
          seed parsed.1.2 rich).1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+46,d,?_⟩
  intro frame parsed hParsed seed rich
  have hRun := run_usage seed parsed.1.2 rich
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  dsimp only at hRun hCalc
  nlinarith only [hRun,hCalc,hOne]

theorem accepted_run_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (run seed parsed.1.2 rich).1.2 ≤
        2000000200*(frame.length+3)^7+
          BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
            seed.width seed.cap.value+2*seed.width+120+C*(frame.length+3)^d := by
  obtain ⟨C,d,hExtra⟩ := accepted_run_usage_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  have he := hExtra frame parsed hParsed seed rich
  have ho := BinaryPhysicalHeapRequestLifetime.accepted_run_usage
    frame parsed hParsed seed rich
  rw [← BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork_erases] at ho
  omega

theorem accepted_run_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ),
      let B := 2000000200*(frame.length+3)^7+
        BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
          seed.width seed.cap.value+2*seed.width+120+C*(frame.length+3)^d
      retainedHeap borrowed (run seed parsed.1.2 rich).1.2 steps ≤ borrowed+B ∧
        framePeak ((run seed parsed.1.2 rich).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_run_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich) borrowed steps

theorem nativeAtMeasured_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtMeasured seed request rich pc hp).1 = nativeAt seed request rich pc hp := rfl

theorem nativeAtMeasured_charges (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtMeasured seed request rich pc hp).2 =
      ((sourceAtTraceMeasured seed request rich pc hp).1.2,(sourceAtTraceMeasured seed request rich pc hp).2) := by
  rw [nativeAtMeasured_eq_reference]
  unfold nativeAtMeasuredReference
  dsimp only
  split <;> rfl

theorem nativeAtMeasured_old_extras (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtMeasured seed request rich pc hp).2.1 = (sourceAtMeasured seed request rich pc hp).2 := by
  rw [nativeAtMeasured_charges]
  rfl

theorem nativeAtMeasured_source_emission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtMeasured seed request rich pc hp).2.2 = (sourceAtTraceMeasured seed request rich pc hp).2 := by
  rw [nativeAtMeasured_charges]

theorem nativeAt_source_work_le (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).2 ≤ (nativeAt seed request rich pc hp).2 := by
  rw [nativeAt_eq_source_reference]
  unfold nativeAtSourceReference
  dsimp only
  split <;> dsimp only <;> omega

theorem nativeAtMeasured_total (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAt seed request rich pc hp).2+(nativeAtMeasured seed request rich pc hp).2.1+
      (nativeAtMeasured seed request rich pc hp).2.2 ≤
        16*(nativeAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+16*n+10 := by
  have hSource := sourceAtTraceMeasured_total_dimension seed request rich pc hp
  have hWork := nativeAt_source_work_le seed request rich pc hp
  rw [nativeAtMeasured_charges]
  change (nativeAt seed request rich pc hp).2+(sourceAtMeasured seed request rich pc hp).2+
    (sourceAtTraceMeasured seed request rich pc hp).2 ≤ _
  change (sourceAt seed request rich pc hp).2+(sourceAtMeasured seed request rich pc hp).2+
    (sourceAtTraceMeasured seed request rich pc hp).2 ≤
      16*(sourceAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+16*n+10 at hSource
  omega

theorem nativeAtWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithWrites seed request rich pc hp).1 = nativeAtMeasured seed request rich pc hp := rfl

theorem nativeAtWithWrites_write_charge (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithWrites seed request rich pc hp).2 = (sourceAtTraceWithWrites seed request rich pc hp).2 := by
  rw [nativeAtWithWrites_eq_reference]
  unfold nativeAtWithWritesReference
  dsimp only
  split <;> rfl

theorem nativeAtWithWrites_write_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithWrites seed request rich pc hp).2 ≤ 32*(nativeAt seed request rich pc hp).2 := by
  rw [nativeAtWithWrites_write_charge]
  have h := sourceAtTraceWithWrites_write_bound seed request rich pc hp
  have hw := nativeAt_source_work_le seed request rich pc hp
  omega

theorem nativeAtWithEmission_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).1 = nativeAtWithWrites seed request rich pc hp := rfl

theorem nativeAtWithEmission_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).2 ≤
      80*(nativeAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length := by
  change (nativeAtWithEmission seed request rich pc hp).2 ≤
    80*(nativeAtWithEmission seed request rich pc hp).1.1.1.2+
      5*(sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2.length
  unfold nativeAtWithEmission
  dsimp only
  split
  · dsimp only
    have h := BinaryTracePlanMeasured.emitFull_total
      (.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2)) []
      (16*((sourceAtTraceWithWrites seed request rich pc hp).1.1.1.2+2)+
        (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2.length) (by
          simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
          omega)
    omega
  · rename_i finished hFinished
    dsimp only
    let terminal := BinaryHeapMaterializationPlan.materializeAt
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length)
      (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1
      (sourceAt_cap seed request rich pc hp) finished 2
    have hb := BinaryHeapMaterializationPlan.materializeAt_budget
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length)
      (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1
      (sourceAt_cap seed request rich pc hp) finished 2
    have h := BinaryTracePlanMeasured.emitFull_total
      (.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2) terminal.1.2)) []
      (16*((sourceAtTraceWithWrites seed request rich pc hp).1.1.1.2+terminal.2+4)+
        (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2.length) (by
          change BinaryTracePlanMeasured.payload terminal.1.2+BinaryTracePlanMeasured.nodes terminal.1.2 ≤ 16*(terminal.2+1) at hb
          simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
          omega)
    dsimp only [terminal] at h
    omega

theorem native_trace_length (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAt seed request rich pc hp).1.2.length ≤
      16*(nativeAt seed request rich pc hp).2+(sourceAt seed request rich pc hp).1.2.length := by
  change (nativeAtWithEmission seed request rich pc hp).1.1.1.1.2.length ≤
    16*(nativeAtWithEmission seed request rich pc hp).1.1.1.2+
      (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2.length
  unfold nativeAtWithEmission
  dsimp only
  split
  · simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
      BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
    omega
  · rename_i finished hFinished
    have h := BinaryHeapMaterializationPlan.materializeAt_budget
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length)
      (sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1
      (sourceAt_cap seed request rich pc hp) finished 2
    simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
      BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
    omega

theorem runWithCharges_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).1 = run seed request rich := rfl

theorem native_work_le_run (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (nativeAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).2 ≤ (run seed request rich).2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  omega

theorem runWithCharges_fields (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let child := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
    let charges := (runWithCharges seed request rich).2
    charges.primitive = child.1.1.2.1 ∧ charges.coinSource = child.1.1.2.2 ∧
      charges.write = child.1.2 ∧ charges.native = child.2 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_wrapper_emission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).2.wrappers ≤
      5*(nativeAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).1.2.length+40 := by
  let child := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation seed.cap.bits.length,.frames (seed.cap.bits.length+2),.arrayAllocation 16,
      .frames 4,.arrayAllocation 24]) (.shifted 4 child.1.1.1.1.2)
  have h := BinaryTracePlanMeasured.emitFull_total plan [] (child.1.1.1.1.2.length+8) (by
    simp only [plan,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
    omega)
  change (BinaryTracePlanMeasured.emitFull plan []).1.2+(BinaryTracePlanMeasured.emitFull plan []).2 ≤ _
  change (BinaryTracePlanMeasured.emitFull plan []).1.2+(BinaryTracePlanMeasured.emitFull plan []).2 ≤
    5*child.1.1.1.1.2.length+40
  omega

end Blotto.BinaryPhysicalHeapAllowanceRequest
