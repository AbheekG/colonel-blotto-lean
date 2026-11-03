import Blotto.BinaryPhysicalBuildAllowanceLifetime
import Blotto.BinaryPhysicalHeapRequestLifetime
import Blotto.BinaryPhysicalBuildAllowanceMeasured
import Blotto.BinaryHeapLoopFusedMeasured
import Blotto.BinaryHeapLoopPrimitiveMeasured

/-! A one-pass physical initializer and resource source consuming the traced
Boolean builder allowance. The encoded builder charge stays separate from
the natural source-work observer, so this data path adds no native decoder.
The selected complete source joins initialization and the internal resource
plan before one outer emission, forwarding reached coin emission and that
actual emission charge separately from the old full record. New cost bounds
explicitly retain trace length. Prior entry points remain proof references. -/

namespace Blotto.BinaryPhysicalHeapAllowanceInitial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPhysicalHeapInitialLifetime
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ}

theorem framePeak_le_under (depth : ℕ) (trace : Trace) :
    framePeak trace ≤ framePeak (under depth trace) := by
  induction trace with
  | nil => simp [under,framePeak]
  | cons e rest ih =>
      cases e <;> simp only [under,List.map_cons,shiftEvent,framePeak] at ih ⊢ <;> omega

theorem wrap_head_delta (slots frames : ℕ) (before after : Trace) (rest : List Trace)
    (A F : ℕ)
    (hCells : BinaryPRGHeapPrimitiveLifetime.cells after ≤
      BinaryPRGHeapPrimitiveLifetime.cells before+A)
    (hFrame : framePeak after ≤ framePeak before+F) :
    BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames (after :: rest)) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames (before :: rest))+A ∧
      framePeak (wrap slots frames (after :: rest)) ≤
        framePeak (wrap slots frames (before :: rest))+F+2 := by
  have hNew := framePeak_under 2 after
  have hOld := framePeak_le_under 2 before
  simp only [wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold BinaryPRGHeapPrimitiveLifetime.cells at hCells
  exact ⟨by omega,by omega⟩

theorem wrap_second_delta (slots frames : ℕ) (first before after : Trace)
    (A F : ℕ)
    (hCells : BinaryPRGHeapPrimitiveLifetime.cells after ≤
      BinaryPRGHeapPrimitiveLifetime.cells before+A)
    (hFrame : framePeak after ≤ framePeak before+F) :
    BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames [first,after]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames [first,before])+A ∧
      framePeak (wrap slots frames [first,after]) ≤
        framePeak (wrap slots frames [first,before])+F+2 := by
  have hNew := framePeak_under 2 after
  have hOld := framePeak_le_under 2 before
  simp only [wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold BinaryPRGHeapPrimitiveLifetime.cells at hCells
  exact ⟨by omega,by omega⟩

theorem calculator_wrap_delta (before calculated : Trace) :
    BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [before,calculated]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells before+
          (32+BinaryPRGHeapPrimitiveLifetime.cells calculated) ∧
      framePeak (wrap 32 2 [before,calculated]) ≤
        framePeak before+(framePeak calculated+2) := by
  have hBefore := framePeak_under 2 before
  have hCalculated := framePeak_under 2 calculated
  simp only [wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

theorem initialFromArrays_trace_delta
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (before after : Trace) (A F : ℕ)
    (hCells : BinaryPRGHeapPrimitiveLifetime.cells after ≤
      BinaryPRGHeapPrimitiveLifetime.cells before+A)
    (hFrame : framePeak after ≤ framePeak before+F) :
    BinaryPRGHeapPrimitiveLifetime.cells (initialFromArraysWithTraceAndWork
      capacity resource hC hR built hBuilt after).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells (initialFromArraysWithTraceAndWork
          capacity resource hC hR built hBuilt before).1.2+A ∧
      framePeak (initialFromArraysWithTraceAndWork
        capacity resource hC hR built hBuilt after).1.2 ≤
        framePeak (initialFromArraysWithTraceAndWork
          capacity resource hC hR built hBuilt before).1.2+F+2 := by
  subst built
  unfold initialFromArraysWithTraceAndWork
  dsimp only
  exact wrap_head_delta 32 2 before after _ A F hCells hFrame

/-- A specification observer for the calculator work on the heaps returned by
the same physical build. It is not an additional build in the producer. -/
def calculationWork (capacity resource : List SignedWord) : ℕ :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
  (BinaryPhysicalBuildAllowance.calculateWithWork raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape).2

def calculationTrace (capacity resource : List SignedWord) : Trace :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
  (BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape).2

def initialFromWordsReference
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) ×
      List Bool) × Trace) × ℕ :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  let calculated := BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let initialized := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords
      hCapacity hResource) (wrap 32 2 [raw.2,calculated.2])
  let calculatorWork := (BinaryPhysicalBuildAllowance.calculateWithWork raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape).2
  (((initialized.1.1,calculated.1),wrap 32 2 [readTrace,initialized.1.2]),
    initialized.2+calculatorWork)

/- The selected initializer consumes one measured allowance calculation. The
former two-observer producer above is retained only as a proof reference. -/
def initialFromWords
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) ×
      List Bool) × Trace) × ℕ :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  let calculated := BinaryPhysicalBuildAllowanceMeasured.calculate raw.1.1
    raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let initialized := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords hCapacity hResource)
    (wrap 32 2 [raw.2,calculated.1.2])
  (((initialized.1.1,calculated.1.1),wrap 32 2 [readTrace,initialized.1.2]),initialized.2+calculated.2)

theorem initialFromWords_eq_reference
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) (readTrace : Trace) :
    initialFromWords capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace =
      initialFromWordsReference capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace := by
  simp only [initialFromWords,initialFromWordsReference,
    BinaryPhysicalBuildAllowanceMeasured.calculate_erases,BinaryPhysicalBuildAllowanceMeasured.calculate_work]

theorem initialFromWords_data
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords
      hCapacity hResource readTrace).1.1.1 =
      (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
        capacityWords resourceWords hCapacity hResource readTrace).1.1 := rfl

theorem initialFromWords_allowance_value
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) (readTrace : Trace) :
    BinaryBigEndian.littleValue (initialFromWords capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).1.1.2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        capacityWords resourceWords).2 := by
  rw [initialFromWords_eq_reference]
  have h := BinaryPhysicalBuildAllowanceLifetime.rawArraysWithTraceAndAllowance_value
    capacityWords resourceWords
  exact h

theorem initialFromWords_work
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) (readTrace : Trace) :
    (initialFromWords capacity resource hC hR capacityWords resourceWords
      hCapacity hResource readTrace).2 =
      (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
        capacityWords resourceWords hCapacity hResource readTrace).2+
        calculationWork capacityWords resourceWords := by
  rw [initialFromWords_eq_reference]
  rfl

theorem initialFromWords_trace_delta
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) (readTrace : Trace) :
    let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
    let calculated := BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace
      raw.1.1 raw.1.2.1.heap.tape raw.1.2.2.heap.tape
    BinaryPRGHeapPrimitiveLifetime.cells (initialFromWords capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells (initialFromReadbackWordsWithTraceAndWork
          capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated.2 ∧
      framePeak (initialFromWords capacity resource hC hR
        capacityWords resourceWords hCapacity hResource readTrace).1.2 ≤
        framePeak (initialFromReadbackWordsWithTraceAndWork
          capacity resource hC hR capacityWords resourceWords hCapacity hResource readTrace).1.2+
          framePeak calculated.2+6 := by
  rw [initialFromWords_eq_reference]
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  let calculated := BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace
    raw.1.1 raw.1.2.1.heap.tape raw.1.2.2.heap.tape
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let hBuilt := castReadbackArrays_value capacity resource capacityWords resourceWords
    hCapacity hResource
  have hRaw := calculator_wrap_delta raw.2 calculated.2
  have hInitial := initialFromArrays_trace_delta capacity resource hC hR built hBuilt
    raw.2 (wrap 32 2 [raw.2,calculated.2])
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated.2)
    (framePeak calculated.2+2) hRaw.1 hRaw.2
  have hOuter := wrap_second_delta 32 2 readTrace
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt raw.2).1.2
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt
      (wrap 32 2 [raw.2,calculated.2])).1.2
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated.2)
    (framePeak calculated.2+4) hInitial.1 (by omega)
  change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [readTrace,
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt
      (wrap 32 2 [raw.2,calculated.2])).1.2]) ≤
    BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [readTrace,
      (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt raw.2).1.2])+
      32+BinaryPRGHeapPrimitiveLifetime.cells calculated.2 ∧
    framePeak (wrap 32 2 [readTrace,
      (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt
        (wrap 32 2 [raw.2,calculated.2])).1.2]) ≤
      framePeak (wrap 32 2 [readTrace,
        (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt raw.2).1.2])+
        framePeak calculated.2+6
  exact ⟨hOuter.1.trans_eq (by omega),hOuter.2.trans_eq (by omega)⟩

def initialFromRequest (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((Stored (capStore selected.length).tree ×
      Finished (capStore selected.length) n (count selected.length)) × List Bool) × Trace) × ℕ :=
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
  (initialized.1,initialized.2+readback.2)

theorem initialFromRequest_data (request : Request n) (rich : Bool) :
    (initialFromRequest request rich).1.1.1 =
      (initialFromRequestWithTraceAndWork request rich).1.1 := rfl

theorem initialFromRequest_allowance_value (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    BinaryBigEndian.littleValue (initialFromRequest request rich).1.1.2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 := by
  unfold initialFromRequest
  dsimp only
  exact initialFromWords_allowance_value _ _ _ _ _ _ _ _ _

theorem initialFromRequest_work (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (initialFromRequest request rich).2 =
      (initialFromRequestWithTraceAndWork request rich).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  unfold initialFromRequest initialFromRequestWithTraceAndWork
  dsimp only
  rw [initialFromWords_work]
  omega

theorem initialFromRequest_trace_delta (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (initialFromRequest request rich).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (initialFromRequestWithTraceAndWork request rich).1.2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (initialFromRequest request rich).1.2 ≤
        framePeak (initialFromRequestWithTraceAndWork request rich).1.2+
          framePeak calculated+6 := by
  unfold initialFromRequest initialFromRequestWithTraceAndWork
  dsimp only
  exact initialFromWords_trace_delta _ _ _ _ _ _ _ _ _

theorem initialFromRequest_usage (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    usage (initialFromRequest request rich).1.2 ≤
      usage (initialFromRequestWithTraceAndWork request rich).1.2+
        usage (calculationTrace words.1 (if rich then words.1 else words.2))+38 := by
  have h := initialFromRequest_trace_delta request rich
  dsimp only at h ⊢
  unfold usage
  omega

/-- Numerical interpretation of the separated encoded charge is a proof
statement; the initializer itself does not decode the Boolean word. -/
theorem initialFromRequest_total_work (request : Request n) (rich : Bool) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (initialFromRequest request rich).2+
      BinaryBigEndian.littleValue (initialFromRequest request rich).1.1.2 =
      (initialFromRequestWithTraceAndBuildWork request rich).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [initialFromRequest_work,initialFromRequest_allowance_value,
    initialFromRequestWithTraceAndBuildWork_charge]
  omega

def sourceAtReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  let completed := BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp
  ((((capWord,completed.1.1),prepared.1.1.2),
      wrap 32 2 [prepared.1.2,completed.1.2]),prepared.2+completed.2)


/-- The selected source carries the actual resource loop's named extra work. -/
def sourceAtMeasuredReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  let completed := BinaryHeapLoopPrimitiveMeasured.runMeasured
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp
  (((((capWord,completed.1.1.1),prepared.1.1.2),
      wrap 32 2 [prepared.1.2,completed.1.1.2]),prepared.2+completed.1.2),completed.2)


def sourcePlanAtReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Plan) × ℕ) × ℕ) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.1.ruler,prepared.1.1.1.1.size⟩
  let completed := BinaryHeapLoopPrimitiveMeasured.runPlanAt
    seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp (depth+2)
  let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
    (.join (.shifted (depth+2) prepared.1.2) completed.1.1.1.2)
  ((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2)


def sourcePlanWithWritesAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Plan) × ℕ) × ℕ) × ℕ) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
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
  (((((((capWord,completed.1.1.1.1),prepared.1.1.2),plan),prepared.2+completed.1.1.2),completed.1.2),completed.2),returned.2)

def sourcePlanAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Plan) × ℕ) × ℕ) × ℕ :=
  (sourcePlanWithWritesAt seed request rich pc hp depth).1

theorem sourcePlanAt_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    sourcePlanAt seed request rich pc hp depth = sourcePlanAtReference seed request rich pc hp depth := rfl

theorem sourcePlanAt_refines (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryWordCoinSourceMeasured.projected (sourcePlanAt seed request rich pc hp depth).1 =
      BinaryWordCoinSourceMeasured.offset depth (sourceAtMeasuredReference seed request rich pc hp) := by
  simp only [sourcePlanAt_eq_reference,sourcePlanAtReference,sourceAtMeasuredReference,BinaryWordCoinSourceMeasured.projected,
    BinaryWordCoinSourceMeasured.offset,BinaryTracePlanMeasured.denote,
    BinaryHeapLoopPrimitiveMeasured.runPlanAt_data,BinaryHeapLoopPrimitiveMeasured.runPlanAt_trace,
    BinaryHeapLoopPrimitiveMeasured.runPlanAt_work,BinaryHeapLoopPrimitiveMeasured.runPlanAt_extra,
    wrap,combine,BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose,List.append_nil]
  rfl

def sourceAtTraceMeasuredReference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let planned := sourcePlanAt seed request rich pc hp 0
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  ((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2)


def sourceAtTraceWithWrites (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  let returned := sourcePlanWithWritesAt seed request rich pc hp 0
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  (((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2)

def sourceAtTraceMeasured (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  (sourceAtTraceWithWrites seed request rich pc hp).1

theorem sourceAtTraceMeasured_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    sourceAtTraceMeasured seed request rich pc hp = sourceAtTraceMeasuredReference seed request rich pc hp := rfl

def sourceAtMeasured (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ) × ℕ :=
  (sourceAtTraceMeasured seed request rich pc hp).1

theorem sourceAtMeasured_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    sourceAtMeasured seed request rich pc hp = sourceAtMeasuredReference seed request rich pc hp := by
  simpa only [sourceAtMeasured,sourceAtTraceMeasured_eq_reference,sourceAtTraceMeasuredReference,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,BinaryWordCoinSourceMeasured.projected,
    BinaryWordCoinSourceMeasured.offset,BinaryTraceDepth.under_zero] using
      sourcePlanAt_refines seed request rich pc hp 0

def sourceAt (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × List Bool) × Trace) × ℕ :=
  (sourceAtMeasured seed request rich pc hp).1

theorem sourceAtMeasured_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtMeasured seed request rich pc hp).1 = sourceAt seed request rich pc hp := rfl


theorem sourceAt_eq_reference (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    sourceAt seed request rich pc hp = sourceAtReference seed request rich pc hp := by
  simp only [sourceAt,sourceAtMeasured_eq_reference,sourceAtMeasuredReference,sourceAtReference,
    BinaryHeapLoopPrimitiveMeasured.runMeasured_compat,BinaryHeapLoopPrimitiveMeasured.run_eq_reference]

theorem sourceAtMeasured_extras_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtMeasured seed request rich pc hp).2 ≤ 5*(sourceAt seed request rich pc hp).2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  have h := BinaryHeapLoopPrimitiveMeasured.runMeasured_extras_bound seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp
  simp only [BinaryHeapLoopPrimitiveMeasured.run] at h
  simp only [sourceAt,sourceAtMeasured_eq_reference,sourceAtMeasuredReference]
  dsimp only [selected,prepared] at h
  omega

theorem sourceAt_with_extras_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).2+(sourceAtMeasured seed request rich pc hp).2 ≤
      6*(sourceAt seed request rich pc hp).2 := by
  have h := sourceAtMeasured_extras_bound seed request rich pc hp
  omega

theorem sourceAt_data (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).1.1.1 =
      (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
        seed request rich pc hp).1.1 := by
  rw [sourceAt_eq_reference]
  rfl

theorem sourceAt_allowance (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).1.1.2 =
      (initialFromRequest request rich).1.1.2 := rfl

theorem sourceAt_cap (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).1.1.1.1 =
      (capStore (BinaryPRGResourceWork.resourceInput request.logical.request rich).length).cap := by
  have h := congrArg Prod.fst (sourceAt_data seed request rich pc hp)
  exact h.trans (BinaryPhysicalHeapRequestLifetime.sourceAt_cap seed request rich pc hp)

theorem sourceAt_allowance_value (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    BinaryBigEndian.littleValue (sourceAt seed request rich pc hp).1.1.2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 := by
  rw [sourceAt_allowance]
  exact initialFromRequest_allowance_value request rich

theorem sourceAt_work (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (sourceAt seed request rich pc hp).2 =
      (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
        seed request rich pc hp).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [sourceAt_eq_reference]
  unfold sourceAtReference BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
  dsimp only
  rw [initialFromRequest_data,initialFromRequest_work]
  omega

theorem sourceAt_total_work (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    (sourceAt seed request rich pc hp).2+
      BinaryBigEndian.littleValue (sourceAt seed request rich pc hp).1.1.2 =
      (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndBuildWork
        seed request rich pc hp).2+
        calculationWork words.1 (if rich then words.1 else words.2) := by
  rw [sourceAt_work,sourceAt_allowance,initialFromRequest_allowance_value,
    BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndBuildWork_charge]
  omega

theorem sourceAt_trace_delta (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
    BinaryPRGHeapPrimitiveLifetime.cells (sourceAt seed request rich pc hp).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
            seed request rich pc hp).1.2+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (sourceAt seed request rich pc hp).1.2 ≤
        framePeak (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
          seed request rich pc hp).1.2+framePeak calculated+8 := by
  rw [sourceAt_eq_reference]
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequestWithTraceAndWork request rich
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request).1.1.getD ([],[])
  let calculated := calculationTrace words.1 (if rich then words.1 else words.2)
  let completed := BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed prepared.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.2 pc hp
  have hInitial := initialFromRequest_trace_delta request rich
  have hw := wrap_head_delta 32 2 prepared.1.2
    (initialFromRequest request rich).1.2 [completed.1.2]
    (32+BinaryPRGHeapPrimitiveLifetime.cells calculated)
    (framePeak calculated+6)
    (by simpa only [prepared,calculated,words,Nat.add_assoc] using hInitial.1)
    (by simpa only [prepared,calculated,words,Nat.add_assoc] using hInitial.2)
  change BinaryPRGHeapPrimitiveLifetime.cells
      (wrap 32 2 [(initialFromRequest request rich).1.2,completed.1.2]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [prepared.1.2,completed.1.2])+
          32+BinaryPRGHeapPrimitiveLifetime.cells calculated ∧
      framePeak (wrap 32 2 [(initialFromRequest request rich).1.2,completed.1.2]) ≤
        framePeak (wrap 32 2 [prepared.1.2,completed.1.2])+framePeak calculated+8
  exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem sourceAt_usage (seed : BinarySeedLookupTree.Store) (request : Request n)
    (rich : Bool) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      request).1.1.getD ([],[])
    usage (sourceAt seed request rich pc hp).1.2 ≤
      usage (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
        seed request rich pc hp).1.2+
        usage (calculationTrace words.1 (if rich then words.1 else words.2))+40 := by
  have h := sourceAt_trace_delta seed request rich pc hp
  dsimp only at h ⊢
  unfold usage
  omega

theorem usage_second_le_wrap (first second : Trace) :
    usage second ≤ usage (wrap 32 2 [first,second]) := by
  have hFrame := framePeak_le_under 2 second
  simp only [usage,wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  omega

theorem calculationTrace_usage_le_builder (capacity resource : List SignedWord) :
    usage (calculationTrace capacity resource) ≤
      usage (BinaryPhysicalBuildAllowanceLifetime.rawArraysWithTraceAndAllowance
        capacity resource).2 :=
  usage_second_le_wrap _ _

theorem accepted_calculationTrace_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool,
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])
      usage (calculationTrace words.1 (if rich then words.1 else words.2)) ≤
        C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPhysicalBuildAllowanceLifetime.accepted_readback_usage_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich
  exact (calculationTrace_usage_le_builder _ _).trans (hBound frame parsed hParsed rich)

theorem accepted_source_work_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
      (sourceAt seed parsed.1.2 rich pc hp).2+
        BinaryBigEndian.littleValue (sourceAt seed parsed.1.2 rich pc hp).1.1.2 ≤
        (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndBuildWork
          seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPhysicalBuildAllowance.accepted_readback_calculation_work_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  rw [sourceAt_total_work]
  exact Nat.add_le_add_left (hBound frame parsed hParsed rich) _

theorem accepted_source_usage_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
      usage (sourceAt seed parsed.1.2 rich pc hp).1.2 ≤
        usage (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
          seed parsed.1.2 rich pc hp).1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_calculationTrace_polynomial
  refine ⟨C+40,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have hSource := sourceAt_usage seed parsed.1.2 rich pc hp
  have hCalc := hBound frame parsed hParsed rich
  have hOne := Nat.one_le_pow d (frame.length+3) (by omega)
  dsimp only at hSource hCalc
  nlinarith only [hSource,hCalc,hOne]

theorem accepted_source_input_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
      let request := parsed.1.2.logical.request
      let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
        request.source.normalizedInput.latticeDenominator
      usage (sourceAt seed parsed.1.2 rich pc hp).1.2 ≤
        2000000200*(frame.length+3)^7+
          BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1 W (binaryWordWidth parsed.1.1)+
          BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W
            request.source.normalizedInput.latticeDenominator seed.width seed.cap.value+76+
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hExtra⟩ := accepted_source_usage_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have he := hExtra frame parsed hParsed seed rich pc hp
  have ho := BinaryPhysicalHeapRequestLifetime.accepted_sourceAt_input_usage
    frame parsed hParsed seed rich pc hp
  change usage (BinaryPhysicalHeapRequestLifetime.sourceAtWithTraceAndWork
    seed parsed.1.2 rich pc hp).1.2 ≤ _ at ho
  dsimp only at ho ⊢
  omega

theorem accepted_source_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
        (borrowed steps : ℕ),
      let request := parsed.1.2.logical.request
      let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
        request.source.normalizedInput.latticeDenominator
      let B := 2000000200*(frame.length+3)^7+
        BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1 W (binaryWordWidth parsed.1.1)+
        BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W
          request.source.normalizedInput.latticeDenominator seed.width seed.cap.value+76+
        C*(frame.length+3)^d
      retainedHeap borrowed (sourceAt seed parsed.1.2 rich pc hp).1.2 steps ≤ borrowed+B ∧
        framePeak ((sourceAt seed parsed.1.2 rich pc hp).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_source_input_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed seed rich pc hp) borrowed steps

theorem sourceAtTraceMeasured_source (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceMeasured seed request rich pc hp).1.1 = sourceAt seed request rich pc hp := rfl

theorem sourcePlanAt_nodes (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.nodes (sourcePlanAt seed request rich pc hp depth).1.1.1.2 ≤
      8*(initialFromRequest request rich).1.1.1.2.active.length+5 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  have h := BinaryHeapLoopPrimitiveMeasured.loopPlanAt_nodes seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2.active prepared.1.1.1.2 pc hp (depth+2)
  simp only [sourcePlanAt_eq_reference,sourcePlanAtReference,BinaryHeapLoopPrimitiveMeasured.runPlanAt,BinaryTracePlanMeasured.nodes]
  dsimp only [selected,prepared] at h
  omega

theorem sourcePlanAt_child_emission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanAt seed request rich pc hp depth).2 ≤ 10*(sourcePlanAt seed request rich pc hp depth).1.1.2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  have h := BinaryHeapLoopPrimitiveMeasured.loopPlanAt_child_emission seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2.active prepared.1.1.1.2 pc hp (depth+2)
  simp only [sourcePlanAt_eq_reference,sourcePlanAtReference,BinaryHeapLoopPrimitiveMeasured.runPlanAt]
  dsimp only [selected,prepared] at h
  omega

theorem sourceAtTraceMeasured_emission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceMeasured seed request rich pc hp).2 ≤
      10*(sourceAtTraceMeasured seed request rich pc hp).1.1.2+
        5*(sourceAtTraceMeasured seed request rich pc hp).1.1.1.2.length+
          16*(initialFromRequest request rich).1.1.1.2.active.length+10 := by
  have hn := sourcePlanAt_nodes seed request rich pc hp 0
  have hc := sourcePlanAt_child_emission seed request rich pc hp 0
  have hs := BinaryTracePlanMeasured.shiftCount_bound (sourcePlanAt seed request rich pc hp 0).1.1.1.2
  simp only [sourceAtTraceMeasured_eq_reference,sourceAtTraceMeasuredReference]
  simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_work,
    BinaryTracePlanMeasured.emitFull_shifts,BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero]
  omega

theorem sourceAtTraceMeasured_total (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceMeasured seed request rich pc hp).1.1.2+
      (sourceAtTraceMeasured seed request rich pc hp).1.2+
      (sourceAtTraceMeasured seed request rich pc hp).2 ≤
        16*(sourceAtTraceMeasured seed request rich pc hp).1.1.2+
          5*(sourceAtTraceMeasured seed request rich pc hp).1.1.1.2.length+
            16*(initialFromRequest request rich).1.1.1.2.active.length+10 := by
  have h := sourceAtMeasured_extras_bound seed request rich pc hp
  change (sourceAtTraceMeasured seed request rich pc hp).1.2 ≤
    5*(sourceAtTraceMeasured seed request rich pc hp).1.1.2 at h
  have he := sourceAtTraceMeasured_emission seed request rich pc hp
  omega

theorem source_plan_references (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.planReferences (sourcePlanAt seed request rich pc hp depth).1.1.1.2 ≤
      16*(initialFromRequest request rich).1.1.1.2.active.length+10 := by
  have h := BinaryTracePlanMeasured.planReferences_bound (sourcePlanAt seed request rich pc hp depth).1.1.1.2
  have hn := sourcePlanAt_nodes seed request rich pc hp depth
  omega

theorem source_emit_frames (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.emitFrames (sourcePlanAt seed request rich pc hp depth).1.1.1.2 ≤
      BinaryTracePlanMeasured.payload (sourcePlanAt seed request rich pc hp depth).1.1.1.2+
        8*(initialFromRequest request rich).1.1.1.2.active.length+6 := by
  have h := BinaryTracePlanMeasured.emitFrames_bound (sourcePlanAt seed request rich pc hp depth).1.1.1.2
  have hn := sourcePlanAt_nodes seed request rich pc hp depth
  omega

theorem source_emission_width (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    binaryWordWidth (sourceAtTraceMeasured seed request rich pc hp).2 ≤
      binaryWordWidth (10*(sourceAtTraceMeasured seed request rich pc hp).1.1.2+
        5*(sourceAtTraceMeasured seed request rich pc hp).1.1.1.2.length+
          16*(initialFromRequest request rich).1.1.1.2.active.length+10) :=
  binaryWordWidth_mono (sourceAtTraceMeasured_emission seed request rich pc hp)

theorem sourcePlanAt_nodes_dimension (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.nodes (sourcePlanAt seed request rich pc hp depth).1.1.1.2 ≤ 8*n+5 := by
  have h := sourcePlanAt_nodes seed request rich pc hp depth
  have hn := (initialFromRequest request rich).1.1.1.2.active_length_le
  omega

theorem sourceAtTraceMeasured_emission_dimension (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceMeasured seed request rich pc hp).2 ≤
      10*(sourceAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+16*n+10 := by
  have h := sourceAtTraceMeasured_emission seed request rich pc hp
  have hn := (initialFromRequest request rich).1.1.1.2.active_length_le
  change (sourceAtTraceMeasured seed request rich pc hp).2 ≤
    10*(sourceAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+
      16*(initialFromRequest request rich).1.1.1.2.active.length+10 at h
  omega

theorem sourceAtTraceMeasured_total_dimension (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed request rich pc hp).2+(sourceAtMeasured seed request rich pc hp).2+
      (sourceAtTraceMeasured seed request rich pc hp).2 ≤
        16*(sourceAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+16*n+10 := by
  have h := sourceAtTraceMeasured_total seed request rich pc hp
  have hn := (initialFromRequest request rich).1.1.1.2.active_length_le
  change (sourceAt seed request rich pc hp).2+(sourceAtMeasured seed request rich pc hp).2+
    (sourceAtTraceMeasured seed request rich pc hp).2 ≤
      16*(sourceAt seed request rich pc hp).2+5*(sourceAt seed request rich pc hp).1.2.length+
        16*(initialFromRequest request rich).1.1.1.2.active.length+10 at h
  omega

theorem sourcePlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).1 = sourcePlanAt seed request rich pc hp depth := rfl

theorem sourceAtTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).1 = sourceAtTraceMeasured seed request rich pc hp := rfl

theorem sourcePlanWithWritesAt_write_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (sourcePlanWithWritesAt seed request rich pc hp depth).2 ≤
      32*(sourcePlanWithWritesAt seed request rich pc hp depth).1.1.1.2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := initialFromRequest request rich
  have h := BinaryHeapLoopPrimitiveMeasured.runPlanWithWritesAt_write_bound seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp (depth+2)
  simp only [sourcePlanWithWritesAt]
  dsimp only [selected,prepared] at h
  omega

theorem sourceAtTraceWithWrites_write_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtTraceWithWrites seed request rich pc hp).2 ≤ 32*(sourceAt seed request rich pc hp).2 :=
  sourcePlanWithWritesAt_write_bound seed request rich pc hp 0

end Blotto.BinaryPhysicalHeapAllowanceInitial
