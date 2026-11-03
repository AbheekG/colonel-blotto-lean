import Blotto.BinaryHeapConstructionPlan
import Blotto.BinaryEnumerationInitial

/-! The raw constructor feeds the actual initializer. Its preceding complete
records and prices are retained exactly, and its source/emission price is
forwarded through the existing physical loop. Native prices remain separate. -/
namespace Blotto.BinaryConstructionInitial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPhysicalHeapInitialLifetime
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {n : ℕ}

theorem cast_value
    (capacity resource : FixedArrayTable n SignedWord)
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (raw : Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler)
    (hRaw : raw = (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).1) :
    castReadbackArrays capacity resource capacityWords resourceWords hCapacity hResource raw hRaw =
      (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1 := by
  subst raw
  exact castReadbackArrays_value capacity resource capacityWords resourceWords hCapacity hResource

def initialFromWords
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :=
  let rawConstruction := BinaryHeapConstructionPlan.rawWithEmission capacityWords resourceWords
  let rawProduced := rawConstruction.1
  let raw := rawProduced.1
  let produced := BinaryBuildAllowancePlan.calculateWithEmission raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let calculated := produced.1
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords))
  let inner := BinaryWrapperEmission.two 32 2 raw.2 calculated.1.2
  let enumerationProduced := BinaryEnumerationInitial.initialFromArraysWithTraceAndWork capacity resource hC hR built
    (cast_value capacity resource capacityWords resourceWords hCapacity hResource raw.1
      (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords)))
    inner.1
  let initializedProduced := enumerationProduced.1
  let initialized := initializedProduced.1
  let outer := BinaryWrapperEmission.two 32 2 readTrace initialized.1.2
  (((((((initialized.1.1,calculated.1.1),outer.1),initialized.2+calculated.2),produced.2),
    rawProduced.2+inner.2+initializedProduced.2+outer.2),enumerationProduced.2),rawConstruction.2)

theorem initialFromWords_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1 = BinaryEnumerationInitial.initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace := by
  have hRaw := BinaryHeapConstructionPlan.raw_compat capacityWords resourceWords
  have hLimits := congrArg (fun out => out.1.1.2.1.heap.tape) hRaw
  have hBids := congrArg (fun out => out.1.1.2.2.heap.tape) hRaw
  simp only [initialFromWords,BinaryEnumerationInitial.initialFromWords]
  rw [hLimits,hBids]
  simp only [BinaryHeapConstructionPlan.raw_compat]

def initialFromRequest (request : Request n) (rich : Bool) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let readProduced := BinaryNumericalReadbackPlan.readPairWithEmission request
  let readback := readProduced.1
  let words := readback.1.1.getD ([],[])
  have hWords : words =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    dsimp only [words,readback,readProduced]
    rw [BinaryNumericalReadbackPlan.readPairWithEmission_compat]
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  have hCapacity : words.1 = selected.length.data.toList := by
    rw [hWords]
    cases rich <;> rfl
  have hResource : (if rich then words.1 else words.2) = selected.resource.data.toList := by
    rw [hWords]
    cases rich <;> rfl
  let construction := initialFromWords selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  let entry := construction.1
  let supplied := entry.1
  let initialized := supplied.1
  (((((initialized.1.1,initialized.1.2+readback.2),initialized.2),supplied.2+readProduced.2),entry.2),construction.2)

theorem initialFromRequest_compat (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).1 = BinaryEnumerationInitial.initialFromRequest request rich := by
  simp only [initialFromRequest,BinaryEnumerationInitial.initialFromRequest,initialFromWords_compat]

def sourcePlanWithWritesAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let construction := initialFromRequest request rich
  let entry := construction.1
  let supplied := entry.1
  let initialized := supplied.1
  let prepared := initialized.1
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  let returned := BinaryHeapLoopPrimitiveMeasured.runPlanWithWritesAt
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp (depth+2)
  let completed := returned.1
  let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
    (.join (.shifted (depth+2) prepared.1.2) completed.1.1.1.2)
  (((((((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2),returned.2),initialized.2),supplied.2),entry.2),construction.2)

theorem sourcePlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).1 =
      BinaryEnumerationInitial.sourcePlanWithWritesAt seed request rich pc hp depth := by
  simp only [sourcePlanWithWritesAt,BinaryEnumerationInitial.sourcePlanWithWritesAt,initialFromRequest_compat]

def sourceAtTraceWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let construction := sourcePlanWithWritesAt seed request rich pc hp 0
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  (((((((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2),child.2),supplied.2),entry.2),construction.2)

theorem sourceAtTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).1 =
      BinaryEnumerationInitial.sourceAtTraceWithWrites seed request rich pc hp := by
  simp only [sourceAtTraceWithWrites,BinaryEnumerationInitial.sourceAtTraceWithWrites,sourcePlanWithWritesAt_compat]

end Blotto.BinaryConstructionInitial
