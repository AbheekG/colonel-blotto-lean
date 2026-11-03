import Blotto.BinaryPhysicalHeapInputLifetime
import Blotto.BinaryPRGHeapInitialLifetimeBound
import Blotto.BinaryHeapScanMeasured
import Blotto.BinaryHeapEnumerationWidthMeasured

/-! The resource-loop initializer can consume an already built certified tree
pair. Equality with the existing array producer is an erased certificate, not
a second heap construction. -/
namespace Blotto.BinaryPhysicalHeapInitialLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {n : ℕ}

def initialFromArraysWithTraceAndWorkReference
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
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
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) :=
    hCap ▸ ids.1
  let measured := BinaryPRGHeapScanComparisonWork.scanWithFullWork
    arrays.1.1 (pack arrays.1.2) addresses
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial
    capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes
      arrays.1.2.heap.tape arrays.1.2.root logical.state.resource :=
    arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,measured,addresses]
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]
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
    dsimp only [addresses,ids]
    rw [hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,
      arrays.1.2.root,arrays.1.2.valid,hResource⟩,
      retained.1,hActive⟩
  (((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),
    wrap 32 2 [arrays.2,ids.2,retained.2]),measured.2.2)


/-- Selected initializer: actual measured enumeration, physical reads and
comparisons return their old trace/work together. The retained reference is
used only in erased refinement proofs. -/
def initialFromArraysWithTraceAndWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
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
  let ids := (BinaryHeapEnumerationWidthMeasured.allFromBits capWord).1
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) :=
    hCap ▸ ids.1
  let measured := BinaryHeapScanMeasured.scan
    arrays.1.1 (pack arrays.1.2) addresses
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial
    capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes
      arrays.1.2.heap.tape arrays.1.2.root logical.state.resource :=
    arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,measured,addresses]
    rw [BinaryHeapScanMeasured.scan_trace]
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
    dsimp only [addresses,ids]
    rw [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,
      arrays.1.2.root,arrays.1.2.valid,hResource⟩,
      retained.1,hActive⟩
  (((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),
    wrap 32 2 [arrays.2,ids.2,retained.2]),measured.2.2)


theorem initialFromArraysWithTraceAndWork_eq_reference
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace =
      initialFromArraysWithTraceAndWorkReference capacity resource hC hR built hBuilt builtTrace := by
  unfold initialFromArraysWithTraceAndWork initialFromArraysWithTraceAndWorkReference
  simp only [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,BinaryHeapScanMeasured.scan_erases]

def initialFromArraysWithTrace
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace :=
  (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1

theorem initialFromArraysWithTraceAndWork_charge
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).2 =
      BinaryPRGHeapInitialLifetime.initialPhysicalScanWork capacity resource := by
  rw [initialFromArraysWithTraceAndWork_eq_reference]
  subst built
  unfold initialFromArraysWithTraceAndWorkReference BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
  rfl

theorem initialFromArrays_erasure
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTrace capacity resource hC hR built hBuilt builtTrace).1 =
      (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).1 := by
  unfold initialFromArraysWithTrace
  rw [initialFromArraysWithTraceAndWork_eq_reference]
  subst built
  unfold initialFromArraysWithTraceAndWorkReference BinaryPRGHeapInitialLifetime.initialWithTrace
  rfl

def castReadbackArrays
    (capacity resource : FixedArrayTable n SignedWord)
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (raw : Σ ruler : List Bool,
      BinaryPhysicalHeapInputLifetime.RawArraysAt capacityWords resourceWords ruler)
    (hRaw : raw = (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      capacityWords resourceWords).1) :
    BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []) :=
  have hRuler : raw.1 = BinaryCarryCounter.count capacity.data.toList [] := by
    rw [hRaw,hCapacity]
    exact (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure capacity.data.toList [])
  have hType : BinaryPhysicalHeapInputLifetime.RawArraysAt
      capacityWords resourceWords raw.1 =
        BinaryPRGHeapInitialLifetime.ArraysAt capacity resource raw.1 := by
    cases hCapacity
    cases hResource
    rfl
  hRuler ▸ (hType ▸ raw.2)

theorem castReadbackArrays_value
    (capacity resource : FixedArrayTable n SignedWord)
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList) :
    castReadbackArrays capacity resource capacityWords resourceWords hCapacity hResource
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).1 rfl =
      (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1 := by
  cases hCapacity
  cases hResource
  unfold castReadbackArrays
  obtain ⟨hRuler,hValue⟩ := BinaryPhysicalHeapInputLifetime.rawArrays_value capacity resource
  exact hValue

def initialFromReadbackWordsWithTraceAndWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1 rfl
  let initialized := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords
      hCapacity hResource) raw.2
  ((initialized.1.1,wrap 32 2 [readTrace,initialized.1.2]),initialized.2)

/-- The same one-pass readback builder, retaining a charge from the heaps it
actually constructs. The selected data and trace are unchanged. -/
def initialFromReadbackWordsWithTraceAndBuildWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let raw := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
    capacityWords resourceWords
  let built := castReadbackArrays capacity resource capacityWords resourceWords
    hCapacity hResource raw.1.1 rfl
  let initialized := initialFromArraysWithTraceAndWork capacity resource hC hR built
    (castReadbackArrays_value capacity resource capacityWords resourceWords
      hCapacity hResource) raw.1.2
  ((initialized.1.1,wrap 32 2 [readTrace,initialized.1.2]),
    initialized.2+raw.2)

theorem initialFromReadbackWordsWithTraceAndBuildWork_erases
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromReadbackWordsWithTraceAndBuildWork capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).1 =
      (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
        capacityWords resourceWords hCapacity hResource readTrace).1 := by
  rfl

theorem initialFromReadbackWordsWithTraceAndBuildWork_charge
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromReadbackWordsWithTraceAndBuildWork capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).2 =
      (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
        capacityWords resourceWords hCapacity hResource readTrace).2+
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        capacityWords resourceWords).2 := by
  rfl

def initialFromReadbackWordsWithTrace
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace :=
  (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
    capacityWords resourceWords hCapacity hResource readTrace).1

theorem initialFromReadbackWordsWithTraceAndWork_charge
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromReadbackWordsWithTraceAndWork capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).2 =
      BinaryPRGHeapInitialLifetime.initialPhysicalScanWork capacity resource := by
  unfold initialFromReadbackWordsWithTraceAndWork
  exact initialFromArraysWithTraceAndWork_charge capacity resource hC hR
    (castReadbackArrays capacity resource capacityWords resourceWords
      hCapacity hResource
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).1 rfl)
    (castReadbackArrays_value capacity resource capacityWords resourceWords
      hCapacity hResource)
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).2

theorem initialFromReadbackWords_erasure
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromReadbackWordsWithTrace capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).1 =
      (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).1 := by
  unfold initialFromReadbackWordsWithTrace initialFromReadbackWordsWithTraceAndWork
  dsimp only
  exact initialFromArrays_erasure capacity resource hC hR
    (castReadbackArrays capacity resource capacityWords resourceWords
      hCapacity hResource
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).1 rfl)
    (castReadbackArrays_value capacity resource capacityWords resourceWords
      hCapacity hResource)
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacityWords resourceWords).2

theorem initialFromArrays_trace
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) :
    (initialFromArraysWithTrace capacity resource hC hR built hBuilt
      (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).2).2 =
      (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 := by
  unfold initialFromArraysWithTrace
  rw [initialFromArraysWithTraceAndWork_eq_reference]
  subst built
  unfold initialFromArraysWithTraceAndWorkReference BinaryPRGHeapInitialLifetime.initialWithTrace
  rfl

theorem initialFromReadbackWords_trace
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList)
    (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) :
    (initialFromReadbackWordsWithTrace capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).2 =
      wrap 32 2 [readTrace,
        (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2] := by
  cases hCapacity
  cases hResource
  unfold initialFromReadbackWordsWithTrace initialFromReadbackWordsWithTraceAndWork
  simp only [BinaryPhysicalHeapInputLifetime.rawArrays_trace]
  simpa only [initialFromArraysWithTrace] using
    congrArg (fun tr => wrap 32 2 [readTrace,tr])
      (initialFromArrays_trace capacity resource hC hR _ _)

/-- The whole initial trace, including enumeration and scan, retains the
output-dependent allowance of the actual two physical heaps. -/
theorem initialWithTrace_returned_build_usage
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      capacity resource hC hR).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          capacity.data.toList resource.data.toList).2) +
      6*n+130+
      BinaryPRGHeapEnumerationLifetime.envelope n (binaryWordWidth n) +
      BinaryPRGHeapScanLifetime.scanEnvelope
        (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)
        (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)
        (binaryWordWidth n) W n + 54 := by
  let B := 33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
      capacity.data.toList resource.data.toList).2) + 6*n+130
  have hRaw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace_usage
    capacity.data.toList resource.data.toList
  rw [BinaryPhysicalHeapInputLifetime.rawArrays_trace] at hRaw
  have hArrays : usage (BinaryPRGHeapInitialLifetime.arraysWithTrace
      capacity resource).2 ≤ B := by
    simpa only [B,Array.length_toList,capacity.size] using hRaw
  exact BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage_of_arrays_bound
    capacity resource hC hR W hW hCapacity hResource B hArrays

def initialFromRequestWithTraceAndWork {n : ℕ} (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((Stored (capStore selected.length).tree ×
      Finished (capStore selected.length) n (count selected.length)) × Trace) × ℕ :=
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
  have hResource : (if rich then words.1 else words.2) =
      selected.resource.data.toList := by
    rw [hWords]
    cases rich <;> rfl
  let initialized := initialFromReadbackWordsWithTraceAndWork selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  (initialized.1,initialized.2+readback.2)

def initialFromRequestWithTraceAndBuildWork {n : ℕ}
    (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((Stored (capStore selected.length).tree ×
      Finished (capStore selected.length) n (count selected.length)) × Trace) × ℕ :=
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
  have hResource : (if rich then words.1 else words.2) =
      selected.resource.data.toList := by
    rw [hWords]
    cases rich <;> rfl
  let initialized := initialFromReadbackWordsWithTraceAndBuildWork
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    words.1 (if rich then words.1 else words.2) hCapacity hResource readback.1.2
  (initialized.1,initialized.2+readback.2)

theorem initialFromRequestWithTraceAndBuildWork_erases {n : ℕ}
    (request : Request n) (rich : Bool) :
    (initialFromRequestWithTraceAndBuildWork request rich).1 =
      (initialFromRequestWithTraceAndWork request rich).1 := by
  rfl

theorem initialFromRequestWithTraceAndBuildWork_charge {n : ℕ}
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (initialFromRequestWithTraceAndBuildWork request rich).2 =
      (initialFromRequestWithTraceAndWork request rich).2+
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2 := by
  unfold initialFromRequestWithTraceAndBuildWork
    initialFromRequestWithTraceAndWork
  dsimp only
  rw [initialFromReadbackWordsWithTraceAndBuildWork_charge]
  omega

/-- Total native allocation performed by the two builders is covered by the
allowance read from their actual physical heaps after request readback. -/
theorem request_readback_build_work_covers_native_allocated {n : ℕ}
    (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    let ruler := BinaryCarryCounter.count selected.length.data.toList []
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler selected.length.data.toList).2.allocatedBits +
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler selected.resource.data.toList).2.allocatedBits ≤
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  have hAlloc := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_covers_native_allocated
    selected.length.data.toList selected.resource.data.toList
  have hRuler :
      (BinaryPRGHeapAllocationLifetime.countWithTrace selected.length.data.toList []).1 =
        BinaryCarryCounter.count selected.length.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure
      selected.length.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure
        selected.length.data.toList [])
  dsimp only at hAlloc
  rw [hRuler] at hAlloc
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  dsimp only
  rw [hWords]
  cases rich <;> simpa [selected,BinaryPRGResourceWork.resourceInput,
    BinaryPRGPreparation.Prepared.rich,BinaryPRGPreparation.Prepared.poor] using hAlloc

/-- The two physical tree builds reached from this request's actual readback
have a work allowance polynomial in dimension and retained tape width. -/
theorem request_readback_build_work_bound {n : ℕ} (request : Request n)
    (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
      words.1 (if rich then words.1 else words.2)).2 ≤
      2*(4*n+1)*
        (BinaryPRGWordStoreHeapMachine.allocationBound
          (BinaryPRGHeapResourceInputBounds.initialHeapBound n
            (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request))+8) := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW : 1 ≤ W :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have hBuild := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_input_bound
    selected.length selected.resource W hW hCapacity hResource
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  dsimp only
  rw [hWords]
  cases rich <;> simpa [selected,W,BinaryPRGResourceWork.resourceInput,
    BinaryPRGPreparation.Prepared.rich,BinaryPRGPreparation.Prepared.poor] using hBuild

theorem request_readback_build_work_le_preparationBound {n : ℕ}
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
      words.1 (if rich then words.1 else words.2)).2 ≤
      BinaryPRGHeapResourceInputBounds.preparationBound n
        (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request) := by
  have hBuild := request_readback_build_work_bound request rich
  unfold BinaryPRGHeapResourceInputBounds.preparationBound
  dsimp only at hBuild ⊢
  omega

theorem request_readback_rawArrays_usage {n : ℕ}
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      words.1 (if rich then words.1 else words.2)).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.countBound words.1.length 0 +
        BinaryPRGHeapResourceInputBounds.preparationBound n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)) +
      6 * words.1.length + 130 := by
  let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
  let words := readback.1.1.getD ([],[])
  have hRaw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace_usage
    words.1 (if rich then words.1 else words.2)
  have hBuild := request_readback_build_work_le_preparationBound request rich
  change (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
    words.1 (if rich then words.1 else words.2)).2 ≤
      BinaryPRGHeapResourceInputBounds.preparationBound n
        (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request) at hBuild
  change usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
    words.1 (if rich then words.1 else words.2)).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.countBound words.1.length 0 +
        BinaryPRGHeapResourceInputBounds.preparationBound n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)) +
      6 * words.1.length + 130
  omega

theorem request_readback_rawArrays_usage_input_bound {n : ℕ}
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      words.1 (if rich then words.1 else words.2)).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
        BinaryPRGHeapResourceInputBounds.preparationBound n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)) +
      6 * n + 130 := by
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  have hLength :
      ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[])).1.length = n := by
    rw [hWords]
    simp only [Array.length_toList,request.logical.request.prepared.lengths.size]
  have h := request_readback_rawArrays_usage request rich
  dsimp only at h ⊢
  rw [hLength] at h
  exact h

theorem request_readback_rawArrays_all_prefix {n : ℕ}
    (request : Request n) (rich : Bool) (borrowed steps : ℕ) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    let B := 33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
      BinaryPRGHeapResourceInputBounds.preparationBound n
        (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)) +
      6 * n + 130
    retainedHeap borrowed (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      words.1 (if rich then words.1 else words.2)).2 steps ≤ borrowed + B ∧
    framePeak ((BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      words.1 (if rich then words.1 else words.2)).2.take steps) ≤ B :=
  all_prefix _ _ (request_readback_rawArrays_usage_input_bound request rich) borrowed steps

theorem initialFromRequestWithTraceAndBuildWork_bound {n : ℕ}
    (request : Request n) (rich : Bool) :
    (initialFromRequestWithTraceAndBuildWork request rich).2 ≤
      (initialFromRequestWithTraceAndWork request rich).2+
        BinaryPRGHeapResourceInputBounds.preparationBound n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request) := by
  rw [initialFromRequestWithTraceAndBuildWork_charge]
  exact Nat.add_le_add_left
    (request_readback_build_work_le_preparationBound request rich) _

def initialFromRequestWithTrace {n : ℕ} (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (Stored (capStore selected.length).tree ×
      Finished (capStore selected.length) n (count selected.length)) × Trace :=
  (initialFromRequestWithTraceAndWork request rich).1

theorem initialFromRequestWithTraceAndWork_charge {n : ℕ}
    (request : Request n) (rich : Bool) :
    (initialFromRequestWithTraceAndWork request rich).2 =
      BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource +
      (2*n+5) := by
  unfold initialFromRequestWithTraceAndWork
  dsimp only
  rw [initialFromReadbackWordsWithTraceAndWork_charge,
    BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork_charge]

theorem initialFromRequest_erasure {n : ℕ} (request : Request n) (rich : Bool) :
    (initialFromRequestWithTrace request rich).1 =
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).1 := by
  unfold initialFromRequestWithTrace initialFromRequestWithTraceAndWork
  exact initialFromReadbackWords_erasure _ _ _ _ _ _ _ _ _

theorem initialFromRequest_trace {n : ℕ} (request : Request n) (rich : Bool) :
    (initialFromRequestWithTrace request rich).2 =
      wrap 32 2
        [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2,
          (BinaryPRGHeapInitialLifetime.initialWithTrace
            (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
            (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
            (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
            (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2] := by
  unfold initialFromRequestWithTrace initialFromRequestWithTraceAndWork
  exact initialFromReadbackWords_trace _ _ _ _ _ _ _ _ _

/-- The selected one-pass initializer carries its readback trace around the
complete initial enumeration and scan trace, while pricing the two builds by
the heaps returned from that readback. -/
theorem initialFromRequestWithTraceAndBuildWork_usage_returned {n : ℕ}
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
    let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
    usage (initialFromRequestWithTraceAndBuildWork request rich).1.2 ≤
      usage (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2 +
      33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2) +
      6*n+130+
      BinaryPRGHeapEnumerationLifetime.envelope n (binaryWordWidth n) +
      BinaryPRGHeapScanLifetime.scanEnvelope K K (binaryWordWidth n) W n + 92 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have hInitial := initialWithTrace_returned_build_usage
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    W hW hCapacity hResource
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  have hBuildEq :
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        selected.length.data.toList selected.resource.data.toList).2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
          request).1.1.getD ([],[])).1
        (if rich then ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
          request).1.1.getD ([],[])).1 else
          ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
            request).1.1.getD ([],[])).2)).2 := by
    rw [hWords]
    cases rich <;> rfl
  rw [hBuildEq] at hInitial
  have hWrap := wrap_usage 32 2
    [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2,
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (initialFromRequestWithTrace request rich).2 ≤ _
  rw [initialFromRequest_trace]
  change usage (wrap 32 2
    [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2,
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2]) ≤
      usage (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2 +
      33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 +
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
            request).1.1.getD ([],[])).1
          (if rich then ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
            request).1.1.getD ([],[])).1 else
            ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
              request).1.1.getD ([],[])).2)).2) +
      6*n+130+
      BinaryPRGHeapEnumerationLifetime.envelope n (binaryWordWidth n) +
      BinaryPRGHeapScanLifetime.scanEnvelope
        (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)
        (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)
        (binaryWordWidth n) W n + 92
  omega

/-- The selected physical initializer's actual retained trace has a bound
computed from the physical stores, including both tree builds and enumeration. -/
theorem initialFromRequest_physical_usage {n : ℕ} (request : Request n)
    (rich : Bool) :
    usage (initialFromRequestWithTrace request rich).2 ≤
      usage (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2 +
        BinaryPRGHeapInitialLifetimeBound.envelope n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)
          (binaryWordWidth n) + 38 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW : 1 ≤ W :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    W hW hCapacity hResource
  rw [initialFromRequest_trace]
  have hWrap := wrap_usage 32 2
    [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).2,
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  dsimp only [selected,W] at hInitial hWrap
  omega

theorem initialFromRequest_physical_envelope {n : ℕ} (request : Request n)
    (rich : Bool) :
    usage (initialFromRequestWithTrace request rich).2 ≤
      BinaryPhysicalNumericalReadbackLifetime.pairEnvelope request +
        BinaryPRGHeapInitialLifetimeBound.envelope n
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)
          (binaryWordWidth n) + 38 := by
  have hInitial := initialFromRequest_physical_usage request rich
  have hRead := BinaryPhysicalNumericalReadbackLifetime.readPair_usage request
  omega

def initialFromParsedWithTrace (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich
    (Stored (capStore selected.length).tree ×
      Finished (capStore selected.length) parsed.1.1 (count selected.length)) × Trace :=
  initialFromRequestWithTrace parsed.1.2 rich

theorem initialFromParsed_physical_usage (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    usage (initialFromParsedWithTrace frame parsed hParsed rich).2 ≤
      2000000200*(frame.length+3)^7+
        BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2)
          (binaryWordWidth parsed.1.1)+38 := by
  have hInitial := initialFromRequest_physical_usage parsed.1.2 rich
  have hRead := BinaryPhysicalNumericalReadbackLifetime.accepted_pair_polynomial_usage
    frame parsed hParsed
  change usage (initialFromRequestWithTrace parsed.1.2 rich).2 ≤ _
  omega

theorem initialFromParsed_physical_prefix (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (borrowed steps : ℕ) :
    let bound := 2000000200*(frame.length+3)^7+
      BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1
        (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2)
        (binaryWordWidth parsed.1.1)+38
    retainedHeap borrowed (initialFromParsedWithTrace frame parsed hParsed rich).2 steps ≤
        borrowed+bound ∧
      framePeak ((initialFromParsedWithTrace frame parsed hParsed rich).2.take steps) ≤
        bound := by
  exact BinaryPRGHeapTraceUsage.all_prefix _ _
    (initialFromParsed_physical_usage frame parsed hParsed rich) borrowed steps

theorem initialFromParsed_erasure (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    (initialFromParsedWithTrace frame parsed hParsed rich).1 =
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1 := by
  unfold initialFromParsedWithTrace
  exact initialFromRequest_erasure parsed.1.2 rich

theorem initialFromParsed_trace (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    (initialFromParsedWithTrace frame parsed hParsed rich).2 =
      wrap 32 2
        [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace parsed.1.2).2,
          (BinaryPRGHeapInitialLifetime.initialWithTrace
            (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
            (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
            (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
            (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2] := by
  unfold initialFromParsedWithTrace
  exact initialFromRequest_trace parsed.1.2 rich

theorem initialFromParsed_usage (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (I : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I) :
    usage (initialFromParsedWithTrace frame parsed hParsed rich).2 ≤
      2000000200*(frame.length+3)^7+I+38 := by
  rw [initialFromParsed_trace]
  have hRead := BinaryPhysicalNumericalReadbackLifetime.accepted_pair_polynomial_usage
    frame parsed hParsed
  have hw := wrap_usage 32 2
    [(BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace parsed.1.2).2,
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  omega

theorem initialFromParsed_prefix (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (I borrowed steps : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I) :
    retainedHeap borrowed (initialFromParsedWithTrace frame parsed hParsed rich).2 steps ≤
        borrowed+(2000000200*(frame.length+3)^7+I+38) ∧
      framePeak ((initialFromParsedWithTrace frame parsed hParsed rich).2.take steps) ≤
        2000000200*(frame.length+3)^7+I+38 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (initialFromParsed_usage frame parsed hParsed rich I hInitial) borrowed steps

end Blotto.BinaryPhysicalHeapInitialLifetime
