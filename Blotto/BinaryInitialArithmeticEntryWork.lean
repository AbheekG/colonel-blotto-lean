import Blotto.BinaryControllerArithmeticEntryWork
import Blotto.BinaryWriteContinuationInitial

/-! Proof-only arithmetic entry charges follow the actual initial scan, including
readback and heap construction, then the concrete resource controller. Existing
retained-cell reservations cover this class; native cost interpretation is separate. -/
namespace Blotto.BinaryInitialArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPhysicalHeapInitialLifetime
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {n : ℕ}

def initialArrays
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) : ℕ :=
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
  BinarySelectionArithmeticEntryWork.scan arrays.1.1 (pack arrays.1.2) addresses 0

theorem initialArrays_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    initialArrays capacity resource hC hR built hBuilt builtTrace ≤ 2*listCells (BinaryPrimitiveInitial.initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1.1.1.1.2 := by
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
  have h := BinarySelectionArithmeticEntryWork.scan_emitted arrays.1.1 (pack arrays.1.2) addresses
  dsimp only [arrays,capWord,enumerated,ids,addresses] at h
  simp only [initialArrays,BinaryPrimitiveInitial.initialFromArraysWithTraceAndWork,
    BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def initialWords
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) : ℕ :=
  let rawConstruction := BinaryHeapConstructionPlan.rawWithEmission capacityWords resourceWords
  let rawProduced := rawConstruction.1
  let raw := rawProduced.1
  let produced := BinaryBuildAllowancePlan.calculateWithEmission raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let calculated := produced.1
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords))
  let inner := BinaryWrapperEmission.two 32 2 raw.2 calculated.1.2
  initialArrays capacity resource hC hR built
    (BinaryConstructionInitial.cast_value capacity resource capacityWords resourceWords hCapacity hResource raw.1
      (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords)))
    inner.1

theorem initialWords_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    initialWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace ≤
      2*listCells (BinaryPrimitiveInitial.initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.1.1.1.1.1.2 := by
  let rawConstruction := BinaryHeapConstructionPlan.rawWithEmission capacityWords resourceWords
  let rawProduced := rawConstruction.1
  let raw := rawProduced.1
  let produced := BinaryBuildAllowancePlan.calculateWithEmission raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let calculated := produced.1
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords))
  let inner := BinaryWrapperEmission.two 32 2 raw.2 calculated.1.2
  have h := initialArrays_bound capacity resource hC hR built
    (BinaryConstructionInitial.cast_value capacity resource capacityWords resourceWords hCapacity hResource raw.1
      (congrArg Prod.fst (BinaryHeapConstructionPlan.raw_data capacityWords resourceWords)))
    inner.1
  dsimp only [rawConstruction,rawProduced,raw,produced,calculated,built,inner] at h
  simp only [initialWords,BinaryPrimitiveInitial.initialFromWords,
    BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells] at h ⊢
  omega

def initialRequest (request : Request n) (rich : Bool) : ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let primitiveRead := BinaryPrimitiveReadbackPlan.readPairWithEmission request
  let readProduced := primitiveRead.1
  let readback := readProduced.1
  let words := readback.1.1.getD ([],[])
  have hWords : words =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    dsimp only [words,readback,readProduced,primitiveRead]
    rw [BinaryPrimitiveReadbackPlan.readPair_compat,BinaryNumericalReadbackPlan.readPairWithEmission_compat]
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
  initialWords selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2

theorem initialRequest_bound (request : Request n) (rich : Bool) :
    initialRequest request rich ≤ 2*listCells (BinaryPrimitiveInitial.initialFromRequest request rich).1.1.1.1.1.1.2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let primitiveRead := BinaryPrimitiveReadbackPlan.readPairWithEmission request
  let readProduced := primitiveRead.1
  let readback := readProduced.1
  let words := readback.1.1.getD ([],[])
  have hWords : words =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    dsimp only [words,readback,readProduced,primitiveRead]
    rw [BinaryPrimitiveReadbackPlan.readPair_compat,BinaryNumericalReadbackPlan.readPairWithEmission_compat]
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
  have h := initialWords_bound selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  simpa only [initialRequest,BinaryPrimitiveInitial.initialFromRequest,selected,primitiveRead,readProduced,readback,words] using h

def source (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) : ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let primitive := BinaryPrimitiveInitial.initialFromRequest request rich
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let initialized := supplied.1
  let prepared := initialized.1
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  initialRequest request rich+
    BinaryControllerArithmeticEntryWork.run
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp (depth+2)

theorem source_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    source seed request rich pc hp depth ≤ 2*listCells (denote
      (BinaryWriteContinuationInitial.sourcePlanWithWritesAt seed request rich pc hp depth).1.1.1.1.1.1.1.1.1.1.1.2) := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let primitive := BinaryPrimitiveInitial.initialFromRequest request rich
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let initialized := supplied.1
  let prepared := initialized.1
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  have hi := initialRequest_bound request rich
  have hl := BinaryControllerArithmeticEntryWork.run_bound
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp (depth+2)
  dsimp only [prepared,initialized,supplied,entry,construction,primitive,selected] at hl
  simp only [source,BinaryWriteContinuationInitial.sourcePlanWithWritesAt,denote,
    listCells_append,listCells_under,listCells]
  omega

theorem source_emitted (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    source seed request rich pc hp 0 ≤ 2*listCells
      (BinaryWriteContinuationInitial.sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1.1.1.1.1.2 := by
  have h := source_bound seed request rich pc hp 0
  simpa only [BinaryWriteContinuationInitial.sourceAtTraceWithWrites,emitFull_erases,emit_data,List.append_nil] using h

end Blotto.BinaryInitialArithmeticEntryWork
