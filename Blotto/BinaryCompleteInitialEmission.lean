import Blotto.BinaryInitialWrapperEmission
import Blotto.BinaryAllowanceEmissionInitial

/-! Actual readback, raw-build, scan and initializer wrappers retain all prior
records and calculator emission. Their additional reached emission is returned
separately for complete sampler transport. Native leaves remain separate. -/
namespace Blotto.BinaryCompleteInitialEmission
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPhysicalHeapInitialLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {n : ℕ}

theorem word_emission_bound (raw calculated read initialized : Trace) (rawExtra initializedExtra : ℕ)
    (hRaw : rawExtra ≤ 5*raw.length+26) (hInitial : initializedExtra ≤ 30*initialized.length+27)
    (hBuilt : (BinaryWrapperEmission.two 32 2 raw calculated).1.length ≤ initialized.length) :
    rawExtra+(BinaryWrapperEmission.two 32 2 raw calculated).2+initializedExtra+
      (BinaryWrapperEmission.two 32 2 read initialized).2 ≤
      45*(BinaryWrapperEmission.two 32 2 read initialized).1.length+89 := by
  simp only [BinaryWrapperEmission.two_work,BinaryWrapperEmission.two_length] at hBuilt ⊢
  omega

theorem readback_join_bound (read initialized : Trace) (readExtra initializedExtra : ℕ)
    (hRead : readExtra ≤ 25*read.length+5) (hInitial : initializedExtra ≤ 45*initialized.length+89)
    (hLength : read.length ≤ initialized.length) :
    initializedExtra+readExtra ≤ 70*initialized.length+94 := by omega

def initialFromWords
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :=
  let rawProduced := BinaryInitialWrapperEmission.rawArraysWithEmission capacityWords resourceWords
  let raw := rawProduced.1
  let produced := BinaryBuildAllowancePlan.calculateWithEmission raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let calculated := produced.1
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let inner := BinaryWrapperEmission.two 32 2 raw.2 calculated.1.2
  let initializedProduced := BinaryInitialWrapperEmission.initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords hCapacity hResource)
    inner.1
  let initialized := initializedProduced.1
  let outer := BinaryWrapperEmission.two 32 2 readTrace initialized.1.2
  (((((initialized.1.1,calculated.1.1),outer.1),initialized.2+calculated.2),produced.2),
    rawProduced.2+inner.2+initializedProduced.2+outer.2)

theorem initialFromWords_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1 = BinaryAllowanceEmissionInitial.initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace := by
  have hRaw := BinaryInitialWrapperEmission.rawArraysWithEmission_compat capacityWords resourceWords
  have hLimits := congrArg (fun out : (Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler) × Trace =>
    out.1.2.1.heap.tape) hRaw
  have hBids := congrArg (fun out : (Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler) × Trace =>
    out.1.2.2.heap.tape) hRaw
  simp only [initialFromWords,BinaryAllowanceEmissionInitial.initialFromWords,
    BinaryInitialWrapperEmission.initialFromArrays_compat,BinaryWrapperEmission.two_trace]
  rw [hLimits,hBids]
  simp only [BinaryInitialWrapperEmission.rawArraysWithEmission_compat,
    BinaryInitialWrapperEmission.initialFromArrays_compat]


theorem initialFromWords_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).2 ≤ 45*(initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.1.1.2.length+89 := by
  unfold initialFromWords
  dsimp only
  apply word_emission_bound
  · exact BinaryInitialWrapperEmission.rawArraysWithEmission_bound _ _
  · exact BinaryInitialWrapperEmission.initialFromArrays_bound _ _ _ _ _ _ _
  · exact BinaryInitialWrapperEmission.initialFromArrays_built_length _ _ _ _ _ _ _

theorem initialFromWords_read_length
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    readTrace.length ≤ (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.1.1.2.length := by
  simp only [initialFromWords,BinaryWrapperEmission.two_length]
  omega

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
  let supplied := initialFromWords selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  let initialized := supplied.1
  (((initialized.1.1,initialized.1.2+readback.2),initialized.2),supplied.2+readProduced.2)

theorem initialFromRequest_compat (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).1 = BinaryAllowanceEmissionInitial.initialFromRequest request rich := by
  simp only [initialFromRequest,BinaryAllowanceEmissionInitial.initialFromRequest,
    BinaryNumericalReadbackPlan.readPairWithEmission_compat,initialFromWords_compat]

theorem initialFromRequest_bound (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).2 ≤ 70*(initialFromRequest request rich).1.1.1.2.length+94 := by
  unfold initialFromRequest
  dsimp only
  apply readback_join_bound
  · exact BinaryNumericalReadbackPlan.readPairWithEmission_bound _
  · exact initialFromWords_bound _ _ _ _ _ _ _ _ _
  · exact initialFromWords_read_length _ _ _ _ _ _ _ _ _

def sourcePlanWithWritesAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let supplied := initialFromRequest request rich
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
  (((((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2),returned.2),initialized.2),supplied.2)

theorem sourcePlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).1 =
      BinaryAllowanceEmissionInitial.sourcePlanWithWritesAt seed request rich pc hp depth := by
  simp only [sourcePlanWithWritesAt,BinaryAllowanceEmissionInitial.sourcePlanWithWritesAt,initialFromRequest_compat]

theorem sourcePlanWithWritesAt_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).2 ≤
      70*BinaryTracePlanMeasured.payload (sourcePlanWithWritesAt seed request rich pc hp depth).1.1.1.1.1.1.2+94 := by
  have h := initialFromRequest_bound request rich
  simp only [sourcePlanWithWritesAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def sourceAtTraceWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let supplied := sourcePlanWithWritesAt seed request rich pc hp 0
  let child := supplied.1
  let returned := child.1
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  (((((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2),child.2),supplied.2)

theorem sourceAtTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).1 =
      BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites seed request rich pc hp := by
  simp only [sourceAtTraceWithWrites,BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites,sourcePlanWithWritesAt_compat]

theorem sourceAtTraceWithWrites_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).2 ≤
      70*(sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.2.length+94 := by
  have h := sourcePlanWithWritesAt_bound seed request rich pc hp 0
  simpa only [sourceAtTraceWithWrites,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero] using h

end Blotto.BinaryCompleteInitialEmission
