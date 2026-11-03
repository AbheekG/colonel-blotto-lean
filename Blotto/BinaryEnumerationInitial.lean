import Blotto.BinaryAddressEnumerationPlan
import Blotto.BinaryCompleteInitialEmission

/-! Actual initializer enumeration retains its previous full records and all
previous prices, and forwards its reached guard/carry work, zero-map work and
one plan emission as a new price. Native primitive/metadata prices remain open. -/
namespace Blotto.BinaryEnumerationInitial
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

theorem enumeration_dimension {w : ℕ} (cap : FixedBinaryWord w) (hCap : cap.value = n) (hWidth : w ≤ n+1) :
    (BinaryAddressEnumerationPlan.allFromBits cap).1.2+(BinaryAddressEnumerationPlan.allFromBits cap).2 ≤
      25*(BinaryAddressEnumerationPlan.allFromBits cap).1.1.2.length+100*(n+1)^2 := by
  have h := BinaryAddressEnumerationPlan.allFromBits_total cap
  rw [hCap] at h
  have hm := Nat.mul_le_mul_left n (show 20*(w+1)+4 ≤ 20*(n+2)+4 by omega)
  nlinarith only [h,hm,hWidth]

theorem outer_bound (read initialized : Trace) (price : ℕ)
    (h : price ≤ 25*initialized.length+100*(n+1)^2) :
    price ≤ 25*(BinaryWrapperEmission.two 32 2 read initialized).1.length+100*(n+1)^2 := by
  rw [BinaryWrapperEmission.two_length]
  omega

def initialFromArraysWithTraceAndWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :=
  let arrays :
      (Stored (capStore capacity).tree ×
        Stored (resStore capacity resource).tree) × Trace :=
    (built,builtTrace)
  let capWord : FixedBinaryWord (capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,hBuilt,
      BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let enumerated := BinaryAddressEnumerationPlan.allFromBits capWord
  let ids := enumerated.1.1
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) :=
    hCap ▸ ids.1
  let produced := BinaryInitialScanPlan.scanWithEmission
    arrays.1.1 (pack arrays.1.2) addresses
  let measured := produced.1
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial
    capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes
      arrays.1.2.heap.tape arrays.1.2.root logical.state.resource :=
    arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,measured,produced,addresses]
    rw [BinaryInitialScanPlan.scanWithEmission_compat,BinaryHeapScanMeasured.scan_trace]
    rw [BinaryPRGHeapScanLifetime.scanWithTrace_erasure]
    rw [BinaryPRGHeapResourceLoop.scanWithWork_value arrays.1.1
      (pack arrays.1.2) hResource]
    have hIdsGeneral : ∀ (word : FixedBinaryWord (capStore capacity).width)
        (h : word = (capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1) =
          BinaryPRGWordControllerBooleanResourceInitial.allAddresses
            (capStore capacity) := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure]
      exact BinaryPRGHeapAddressEnumeration.allWithWork_reference
        (capStore capacity)
    have hIds := hIdsGeneral capWord hCap
    dsimp only [addresses,ids,enumerated]
    rw [BinaryAddressEnumerationPlan.allFromBits_compat,BinaryHeapEnumerationWidthMeasured.allFromBits_erases,hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,
      arrays.1.2.root,arrays.1.2.valid,hResource⟩,
      retained.1,hActive⟩
  let emitted := BinarySeedWrapperEmission.three 32 2 arrays.2 ids.2 retained.2
  (((((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),emitted.1),measured.2.2),produced.2+emitted.2),enumerated.1.2+enumerated.2)

theorem initialFromArrays_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1 =
      BinaryInitialWrapperEmission.initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace := by
  simp only [initialFromArraysWithTraceAndWork,BinaryInitialWrapperEmission.initialFromArraysWithTraceAndWork,
    BinaryAddressEnumerationPlan.allFromBits_compat]

theorem initialFromArrays_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).2 ≤
      25*(initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1.1.1.2.length+100*(n+1)^2 := by
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨built.1.ruler,built.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,hBuilt,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  have hValue : capWord.value = n := by rw [hCap,← count capacity]
  have hw := BinaryPRGHeapResourceInputBounds.source_depth capacity
  have hl := Nat.log2_le_self n
  have hWidth : (capStore capacity).width ≤ n+1 := by unfold binaryWordWidth at hw; omega
  have h := enumeration_dimension capWord hValue hWidth
  simp only [initialFromArraysWithTraceAndWork,BinarySeedWrapperEmission.three_length]
  dsimp only [capWord] at h
  omega

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
  let enumerationProduced := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords hCapacity hResource)
    inner.1
  let initializedProduced := enumerationProduced.1
  let initialized := initializedProduced.1
  let outer := BinaryWrapperEmission.two 32 2 readTrace initialized.1.2
  ((((((initialized.1.1,calculated.1.1),outer.1),initialized.2+calculated.2),produced.2),
    rawProduced.2+inner.2+initializedProduced.2+outer.2),enumerationProduced.2)

theorem initialFromWords_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1 = BinaryCompleteInitialEmission.initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace := by
  have hRaw := BinaryInitialWrapperEmission.rawArraysWithEmission_compat capacityWords resourceWords
  have hLimits := congrArg (fun out : (Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler) × Trace =>
    out.1.2.1.heap.tape) hRaw
  have hBids := congrArg (fun out : (Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler) × Trace =>
    out.1.2.2.heap.tape) hRaw
  simp only [initialFromWords,BinaryCompleteInitialEmission.initialFromWords]
  rw [hLimits,hBids]
  simp only [BinaryInitialWrapperEmission.rawArraysWithEmission_compat,initialFromArrays_compat]

theorem initialFromWords_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).2 ≤ 25*(initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.1.1.1.2.length+100*(n+1)^2 := by
  unfold initialFromWords
  dsimp only
  apply outer_bound
  exact initialFromArrays_bound _ _ _ _ _ _ _

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
  let entry := initialFromWords selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  let supplied := entry.1
  let initialized := supplied.1
  ((((initialized.1.1,initialized.1.2+readback.2),initialized.2),supplied.2+readProduced.2),entry.2)

theorem initialFromRequest_compat (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).1 = BinaryCompleteInitialEmission.initialFromRequest request rich := by
  simp only [initialFromRequest,BinaryCompleteInitialEmission.initialFromRequest,initialFromWords_compat]

theorem initialFromRequest_bound (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).2 ≤ 25*(initialFromRequest request rich).1.1.1.1.2.length+100*(n+1)^2 := by
  unfold initialFromRequest
  dsimp only
  exact initialFromWords_bound _ _ _ _ _ _ _ _ _

def sourcePlanWithWritesAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let entry := initialFromRequest request rich
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
  ((((((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2),returned.2),initialized.2),supplied.2),entry.2)

theorem sourcePlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).1 =
      BinaryCompleteInitialEmission.sourcePlanWithWritesAt seed request rich pc hp depth := by
  simp only [sourcePlanWithWritesAt,BinaryCompleteInitialEmission.sourcePlanWithWritesAt,initialFromRequest_compat]

theorem sourcePlanWithWritesAt_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).2 ≤
      25*BinaryTracePlanMeasured.payload (sourcePlanWithWritesAt seed request rich pc hp depth).1.1.1.1.1.1.1.2+100*(n+1)^2 := by
  have h := initialFromRequest_bound request rich
  simp only [sourcePlanWithWritesAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def sourceAtTraceWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let entry := sourcePlanWithWritesAt seed request rich pc hp 0
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  ((((((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2),child.2),supplied.2),entry.2)

theorem sourceAtTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).1 =
      BinaryCompleteInitialEmission.sourceAtTraceWithWrites seed request rich pc hp := by
  simp only [sourceAtTraceWithWrites,BinaryCompleteInitialEmission.sourceAtTraceWithWrites,sourcePlanWithWritesAt_compat]

theorem sourceAtTraceWithWrites_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).2 ≤
      25*(sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1.2.length+100*(n+1)^2 := by
  have h := sourcePlanWithWritesAt_bound seed request rich pc hp 0
  simpa only [sourceAtTraceWithWrites,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero] using h

end Blotto.BinaryEnumerationInitial
