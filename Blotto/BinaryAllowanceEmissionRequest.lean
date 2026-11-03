import Blotto.BinaryAllowanceEmissionInitial
import Blotto.BinaryPhysicalHeapAllowanceRequest

/-! The actual resource request retains the calculator emitter's price through
both materialization branches and the complete preceding ledger. This does not
price the remaining initializer leaves or complete native execution. -/
namespace Blotto.BinaryAllowanceEmissionRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPhysicalHeapAllowanceInitial (sourceAt_cap)
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {n : ℕ}

def nativeAtWithEmission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let child := BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites seed request rich pc hp
  let returned := child.1
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 drawn.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      ((((((((none,drawn.1.1.1.2.2),drawn.1.1.2),emitted.1.1),drawn.2+2),
        (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2)
  | some state =>
      let terminal := BinaryHeapMaterializationPlan.materializeAt selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (by simpa only [drawn,produced,returned,child,BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_compat,
          BinaryPhysicalHeapAllowanceInitial.sourceAt,BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured,
          BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured]
          using sourceAt_cap seed request rich pc hp) state 2
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 drawn.1.2) terminal.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      ((((((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        emitted.1.1),drawn.2+terminal.2+4),
          (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2)

theorem nativeAtWithEmission_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).1 =
      BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed request rich pc hp := by
  simp only [nativeAtWithEmission,BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission,
    BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_compat]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome]

theorem nativeAtWithEmission_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).2 ≤
      50*(nativeAtWithEmission seed request rich pc hp).1.1.1.1.2+5 := by
  have h := BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_bound seed request rich pc hp
  unfold nativeAtWithEmission
  dsimp only
  split <;> dsimp only <;> omega

def runWithCharges (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :=
  let child := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let returned := child.1
  let drawn := returned.1.1.1
  let width := seed.cap.bits.length
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation width,.frames (width+2),.arrayAllocation 16,.frames 4,.arrayAllocation 24])
    (.shifted 4 drawn.1.2)
  let emitted := BinaryTracePlanMeasured.emitFull plan []
  ((((drawn.1.1,emitted.1.1),drawn.2+
      BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      BinaryPhysicalHeapRequestLifetime.preparationResidualAllowance request),
    (⟨returned.1.1.2.1,returned.1.1.2.2,returned.1.2,returned.2,emitted.1.2+emitted.2⟩ : BinaryExecutionCharges.Charges)),child.2)

theorem runWithCharges_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).1 = BinaryPhysicalHeapAllowanceRequest.runWithCharges seed request rich := by
  simp only [runWithCharges,BinaryPhysicalHeapAllowanceRequest.runWithCharges,nativeAtWithEmission_compat]

theorem runWithCharges_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).2 ≤ 50*(runWithCharges seed request rich).1.1.2+5 := by
  have h := nativeAtWithEmission_bound seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  dsimp only [runWithCharges]
  omega

end Blotto.BinaryAllowanceEmissionRequest
