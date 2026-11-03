import Blotto.BinaryBuildAllowancePlan
import Blotto.BinaryPhysicalHeapAllowanceInitial

/-! A concrete initializer/source continuation consumes the actual allowance
emitter once and forwards its returned charge separately. Full preceding
records and existing charge meanings are preserved. Other initializer leaves,
metadata, native runtime and whole-prefix physical space remain separate. -/
namespace Blotto.BinaryAllowanceEmissionInitial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPhysicalHeapInitialLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {n : ℕ}

def initialFromWords
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  let produced := BinaryBuildAllowancePlan.calculateWithEmission raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let calculated := produced.1
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let initialized := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords hCapacity hResource)
    (wrap 32 2 [raw.2,calculated.1.2])
  ((((initialized.1.1,calculated.1.1),wrap 32 2 [readTrace,initialized.1.2]),initialized.2+calculated.2),produced.2)

theorem initialFromWords_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1 = BinaryPhysicalHeapAllowanceInitial.initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace := by
  simp only [initialFromWords,BinaryPhysicalHeapAllowanceInitial.initialFromWords,
    BinaryBuildAllowancePlan.calculateWithEmission_compat]

theorem initialFromWords_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).2 ≤ 50*(initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.2+5 := by
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  have h := BinaryBuildAllowancePlan.calculateWithEmission_bound raw.1.1 raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  change (BinaryBuildAllowancePlan.calculateWithEmission raw.1.1 raw.1.2.1.heap.tape raw.1.2.2.heap.tape).2 ≤ _
  dsimp only [initialFromWords]
  rw [BinaryBuildAllowancePlan.calculateWithEmission_compat]
  dsimp only [raw] at h ⊢
  omega

def initialFromRequest (request : Request n) (rich : Bool) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
  let words := readback.1.1.getD ([],[])
  have hWords : words =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
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
  let initialized := initialFromWords selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  ((initialized.1.1,initialized.1.2+readback.2),initialized.2)

theorem initialFromRequest_compat (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).1 = BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich := by
  simp only [initialFromRequest,BinaryPhysicalHeapAllowanceInitial.initialFromRequest,initialFromWords_compat]

theorem initialFromRequest_bound (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).2 ≤ 50*(initialFromRequest request rich).1.2+5 := by
  unfold initialFromRequest
  dsimp only
  apply (initialFromWords_bound _ _ _ _ _ _ _ _ _).trans
  omega


def sourcePlanWithWritesAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let initialized := initialFromRequest request rich
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
  ((((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2),returned.2),initialized.2)

theorem sourcePlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).1 =
      BinaryPhysicalHeapAllowanceInitial.sourcePlanWithWritesAt seed request rich pc hp depth := by
  simp only [sourcePlanWithWritesAt,BinaryPhysicalHeapAllowanceInitial.sourcePlanWithWritesAt,initialFromRequest_compat]

theorem sourcePlanWithWritesAt_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).2 ≤
      50*(sourcePlanWithWritesAt seed request rich pc hp depth).1.1.1.1.2+5 := by
  have h := initialFromRequest_bound request rich
  dsimp only [sourcePlanWithWritesAt]
  omega

def sourceAtTraceWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let child := sourcePlanWithWritesAt seed request rich pc hp 0
  let returned := child.1
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  ((((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2),child.2)

theorem sourceAtTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).1 =
      BinaryPhysicalHeapAllowanceInitial.sourceAtTraceWithWrites seed request rich pc hp := by
  simp only [sourceAtTraceWithWrites,BinaryPhysicalHeapAllowanceInitial.sourceAtTraceWithWrites,sourcePlanWithWritesAt_compat]

theorem sourceAtTraceWithWrites_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).2 ≤
      50*(sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.2+5 :=
  sourcePlanWithWritesAt_bound seed request rich pc hp 0

end Blotto.BinaryAllowanceEmissionInitial
