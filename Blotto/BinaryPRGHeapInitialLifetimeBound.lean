import Blotto.BinaryPRGHeapInitialLifetime

/-! Original dimension and word widths derive the complete physical
initialization allocation bound, including lists, one ruler, both builds,
Boolean identifiers and the initial fractional scan. -/

namespace Blotto.BinaryPRGHeapInitialLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapInitialLifetime
open BinaryPRGHeapResourceInputBounds (initialHeapBound)
set_option maxHeartbeats 1500000

variable {n : ℕ}

def buildEnvelope (n W : ℕ) : ℕ :=
  33 * ((4 * n + 1) * (BinaryPRGWordStoreHeapMachine.allocationBound (initialHeapBound n W) + 8)) + 28

theorem ruler_build_usage (capacity input : FixedArrayTable n SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hInput : ∀ j,width (input.read j) ≤ W) :
    usage (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero
      (BinaryCarryCounter.count capacity.data.toList []) input.data.toList).2 ≤ buildEnvelope n W := by
  have hHeap := BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity input W hW hInput
  have h := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_usage BinaryRationalOpcode.zero
    (BinaryCarryCounter.count capacity.data.toList []) input.data.toList (initialHeapBound n W) hHeap
  have hNodes := BinaryPRGHeapResourceInputBounds.source_nodes capacity
  unfold buildEnvelope
  exact h.trans (by gcongr)

theorem arraysWithTrace_usage (capacity resource : FixedArrayTable n SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W) :
    usage (arraysWithTrace capacity resource).2 ≤
      33 * BinaryPRGWordStoreHeapMachine.countBound n 0 + 2 * buildEnvelope n W + 6 * n + 74 := by
  have hc := BinaryPRGHeapRulerLifetime.count_usage capacity.data.toList []
  simp only [Array.length_toList,capacity.size,List.length_nil] at hc
  have hLimits := ruler_build_usage capacity capacity W hW hCapacity
  have hBids := ruler_build_usage capacity resource W hW hResource
  have hRuler : (BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []).1 =
      BinaryCarryCounter.count capacity.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure capacity.data.toList [])
  have hTraceC := congrArg (fun ruler => (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero ruler capacity.data.toList).2) hRuler
  have hTraceR := congrArg (fun ruler => (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero ruler resource.data.toList).2) hRuler
  have hw := wrapList_usage (3 * n) 64 (3 * n + 4)
    [(BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []).2,
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero
        (BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []).1 capacity.data.toList).2,
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero
        (BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []).1 resource.data.toList).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [hTraceC,hTraceR] at hw
  unfold arraysWithTrace
  dsimp only
  rw [hTraceC,hTraceR]
  omega

def envelope (n W depth : ℕ) : ℕ :=
  33 * BinaryPRGWordStoreHeapMachine.countBound n 0 + 2 * buildEnvelope n W +
    BinaryPRGHeapEnumerationLifetime.envelope n depth +
    BinaryPRGHeapScanLifetime.scanEnvelope (initialHeapBound n W) (initialHeapBound n W) depth W n + 6 * n + 128

theorem envelope_depth_mono (n W : ℕ) {d e : ℕ} (h : d ≤ e) : envelope n W d ≤ envelope n W e := by
  unfold envelope BinaryPRGHeapEnumerationLifetime.envelope BinaryPRGHeapEnumerationLifetime.localEnvelope
    BinaryPRGHeapScanLifetime.scanEnvelope BinaryPRGHeapScanLifetime.fractionalEnvelope
    BinaryPRGHeapTraceUsage.readEnvelope BinaryPRGHeapStoredTree.readBound
    BinaryPRGWordStoreHeapMachine.lookupBound BinaryPRGWordStoreHeapMachine.lookupAllocation
    BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

/-- The initializer's enumeration and scan trace bound is independent of how
the preceding array-builder trace is bounded. -/
theorem initialWithTrace_usage_of_arrays_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W)
    (B : ℕ) (hArrays : usage (arraysWithTrace capacity resource).2 ≤ B) :
    usage (initialWithTrace capacity resource hC hR).2 ≤
      B + BinaryPRGHeapEnumerationLifetime.envelope n (binaryWordWidth n) +
        BinaryPRGHeapScanLifetime.scanEnvelope (initialHeapBound n W)
          (initialHeapBound n W) (binaryWordWidth n) W n + 54 := by
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (BinaryPRGHeapResourceSource.capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (BinaryPRGWordControllerBooleanResourceUpdate.Address
    (BinaryPRGHeapResourceSource.capStore capacity).width
    (BinaryPRGHeapResourceSource.capStore capacity).cap) := hCap ▸ ids.1
  have hCapValue : capWord.value = n := by
    rw [hCap]
    exact (BinaryPRGHeapResourceSource.count capacity).symm
  have hLength : addresses.length = n := by
    dsimp only [addresses,ids]
    have hGeneral : ∀ (word : FixedBinaryWord
        (BinaryPRGHeapResourceSource.capStore capacity).width)
        (h : word = (BinaryPRGHeapResourceSource.capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1).length = n := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,
        BinaryPRGHeapAddressEnumeration.allWithWork_reference]
      have hLen := congrArg List.length
        (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
          (BinaryPRGHeapResourceSource.capStore capacity))
      simpa only [List.length_map,List.length_range,
        ← BinaryPRGHeapResourceSource.count capacity] using hLen
    exact hGeneral capWord hCap
  have hLimits : arrays.1.1.heap.tape.length ≤ initialHeapBound n W := by
    dsimp only [arrays]
    rw [arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity capacity W hW hCapacity
  have hBids : arrays.1.2.heap.tape.length ≤ initialHeapBound n W := by
    dsimp only [arrays]
    rw [arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity resource W hW hResource
  have hBidWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((BinaryPRGHeapPackedStore.pack arrays.1.2).readWithWork address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width
      capacity resource W hResource address
  have hLimitWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork arrays.1.1 address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width
      capacity capacity W hCapacity address
  have hScan := BinaryPRGHeapScanLifetime.scanWithTrace_usage
    arrays.1.1 (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses
    (initialHeapBound n W) (initialHeapBound n W) W
    hLimits hBids hW hBidWidths hLimitWidths
  rw [hLength] at hScan
  have hIds := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_usage capWord
  have hIds' := hIds.trans_eq (congrArg
    (fun count => BinaryPRGHeapEnumerationLifetime.envelope count
      (BinaryPRGHeapResourceSource.capStore capacity).width) hCapValue)
  have hw := wrap_usage 32 2 [arrays.2,ids.2,
    (BinaryPRGHeapScanLifetime.scanWithTrace arrays.1.1
      (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hBound : usage (initialWithTrace capacity resource hC hR).2 ≤
      B + BinaryPRGHeapEnumerationLifetime.envelope n
        (BinaryPRGHeapResourceSource.capStore capacity).width +
      BinaryPRGHeapScanLifetime.scanEnvelope (initialHeapBound n W)
        (initialHeapBound n W)
        (BinaryPRGHeapResourceSource.capStore capacity).width W n + 54 := by
    unfold initialWithTrace
    change usage (wrap 32 2 [arrays.2,ids.2,
      (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1
        (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).1.2]) ≤ _
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]
    change usage arrays.2 ≤ B at hArrays
    change usage ids.2 ≤ _ at hIds'
    omega
  have hMono := envelope_depth_mono n W
    (BinaryPRGHeapResourceInputBounds.source_depth capacity)
  unfold envelope at hMono
  omega

theorem initialWithTrace_usage (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (W : ℕ) (hW : 1 ≤ W) (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W) :
    usage (initialWithTrace capacity resource hC hR).2 ≤ envelope n W (binaryWordWidth n) := by
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (BinaryPRGHeapResourceSource.capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (BinaryPRGWordControllerBooleanResourceUpdate.Address
    (BinaryPRGHeapResourceSource.capStore capacity).width (BinaryPRGHeapResourceSource.capStore capacity).cap) := hCap ▸ ids.1
  have hCapValue : capWord.value = n := by
    rw [hCap]
    exact (BinaryPRGHeapResourceSource.count capacity).symm
  have hLength : addresses.length = n := by
    dsimp only [addresses,ids]
    have hGeneral : ∀ (word : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width)
        (h : word = (BinaryPRGHeapResourceSource.capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1).length = n := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,BinaryPRGHeapAddressEnumeration.allWithWork_reference]
      have hLen := congrArg List.length (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
        (BinaryPRGHeapResourceSource.capStore capacity))
      simpa only [List.length_map,List.length_range,← BinaryPRGHeapResourceSource.count capacity] using hLen
    exact hGeneral capWord hCap
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound capacity resource hC hR W hW hCapacity hResource
  have hLimits : arrays.1.1.heap.tape.length ≤ initialHeapBound n W := by
    dsimp only [arrays]
    rw [arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity capacity W hW hCapacity
  have hBids : arrays.1.2.heap.tape.length ≤ initialHeapBound n W := by
    dsimp only [arrays]
    rw [arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity resource W hW hResource
  have hBidWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((BinaryPRGHeapPackedStore.pack arrays.1.2).readWithWork address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity resource W hResource address
  have hLimitWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork arrays.1.1 address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity capacity W hCapacity address
  have hScan := BinaryPRGHeapScanLifetime.scanWithTrace_usage arrays.1.1 (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses
    (initialHeapBound n W) (initialHeapBound n W) W hLimits hBids hW hBidWidths hLimitWidths
  rw [hLength] at hScan
  have hArrays := arraysWithTrace_usage capacity resource W hW hCapacity hResource
  have hIds := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_usage capWord
  have hIds' := hIds.trans_eq (congrArg (fun count => BinaryPRGHeapEnumerationLifetime.envelope count
    (BinaryPRGHeapResourceSource.capStore capacity).width) hCapValue)
  have hw := wrap_usage 32 2 [arrays.2,ids.2,
    (BinaryPRGHeapScanLifetime.scanWithTrace arrays.1.1 (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hBound : usage (initialWithTrace capacity resource hC hR).2 ≤
      envelope n W (BinaryPRGHeapResourceSource.capStore capacity).width := by
    unfold initialWithTrace
    change usage (wrap 32 2 [arrays.2,ids.2,
      (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1
        (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).1.2]) ≤ _
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]
    change usage arrays.2 ≤ _ at hArrays
    change usage ids.2 ≤ _ at hIds'
    unfold envelope
    omega
  exact hBound.trans (envelope_depth_mono n W (BinaryPRGHeapResourceInputBounds.source_depth capacity))

theorem initialComparisonWork_bound (capacity resource : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    initialComparisonWork capacity resource ≤ n*1000*(W+1)^2 := by
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (BinaryPRGHeapResourceSource.capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (BinaryPRGWordControllerBooleanResourceUpdate.Address
    (BinaryPRGHeapResourceSource.capStore capacity).width
    (BinaryPRGHeapResourceSource.capStore capacity).cap) := hCap ▸ ids.1
  have hLength : addresses.length = n := by
    dsimp only [addresses,ids]
    have hGeneral : ∀ (word : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width)
        (h : word = (BinaryPRGHeapResourceSource.capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1).length = n := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,
        BinaryPRGHeapAddressEnumeration.allWithWork_reference]
      have hLen := congrArg List.length (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
        (BinaryPRGHeapResourceSource.capStore capacity))
      simpa only [List.length_map,List.length_range,← BinaryPRGHeapResourceSource.count capacity] using hLen
    exact hGeneral capWord hCap
  have hBidWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((BinaryPRGHeapPackedStore.pack arrays.1.2).readWithWork address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity resource W hResource address
  have hLimitWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork arrays.1.1 address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity capacity W hCapacity address
  have hZero : width BinaryRationalOpcode.zero ≤ W := by change 1 ≤ W; exact hW
  have hMeasured := BinaryPRGHeapScanComparisonWork.scanWithWork_bound arrays.1.1
    (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses W
    (by intro address _; exact hBidWidths address)
    (by intro address _; exact hLimitWidths address) hZero
  rw [hLength] at hMeasured
  change (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1
    (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).2.1 ≤ _
  rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_comparison]
  exact hMeasured

theorem initialPhysicalScanWork_bound (capacity resource : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    initialPhysicalScanWork capacity resource ≤
      BinaryPRGHeapResourceUpdateBudget.scanBound
        (initialHeapBound n W) (initialHeapBound n W) (binaryWordWidth n) W n := by
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (BinaryPRGHeapResourceSource.capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (BinaryPRGWordControllerBooleanResourceUpdate.Address
    (BinaryPRGHeapResourceSource.capStore capacity).width
    (BinaryPRGHeapResourceSource.capStore capacity).cap) := hCap ▸ ids.1
  have hLength : addresses.length = n := by
    dsimp only [addresses,ids]
    have hGeneral : ∀ (word : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width)
        (h : word = (BinaryPRGHeapResourceSource.capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1).length = n := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,
        BinaryPRGHeapAddressEnumeration.allWithWork_reference]
      have hLen := congrArg List.length (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
        (BinaryPRGHeapResourceSource.capStore capacity))
      simpa only [List.length_map,List.length_range,← BinaryPRGHeapResourceSource.count capacity] using hLen
    exact hGeneral capWord hCap
  let K := initialHeapBound n W
  have hLimits : arrays.1.1.heap.tape.length ≤ K := by
    dsimp only [arrays,K]
    rw [arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity capacity W hW hCapacity
  have hBids : arrays.1.2.heap.tape.length ≤ K := by
    dsimp only [arrays,K]
    rw [arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity resource W hW hResource
  have hBidWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((BinaryPRGHeapPackedStore.pack arrays.1.2).readWithWork address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_bids_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity resource W hResource address
  have hLimitWidths : ∀ address : BinaryPRGWordControllerBooleanResourceUpdate.Address
      (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork arrays.1.1 address.word).1 ≤ W := by
    intro address
    simp only [arrays,arrays_limits_erasure]
    exact BinaryPRGHeapResourceInputBounds.prepared_read_width capacity capacity W hCapacity address
  have hScan := BinaryPRGHeapScanComparisonWork.scanWithFullWork_bound arrays.1.1
    (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses
  rw [BinaryPRGHeapResourceLoop.scanWorkBound_eq_packed] at hScan
  have hPacked := BinaryPRGHeapResourceInputBounds.scanWorkBoundPacked_bound
    (BinaryPRGHeapPackedStore.pack arrays.1.1)
    (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses K K W
    hLimits hBids hW hBidWidths
    (by
      intro address
      rw [BinaryPRGHeapPackedStore.Packed.readWithWork_stored
        (BinaryPRGHeapPackedStore.pack arrays.1.1) arrays.1.1.realizes address.word]
      exact hLimitWidths address)
  have hDepth := BinaryPRGHeapResourceInputBounds.source_depth capacity
  have hMono := BinaryPRGHeapResourceInputBounds.scanBound_mono
    (W := W) (count := addresses.length) (C := K) (H := K)
    (C' := K) (H' := K)
    le_rfl le_rfl hDepth
  rw [hLength] at hMono
  rw [hLength] at hPacked
  change (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1
    (BinaryPRGHeapPackedStore.pack arrays.1.2) addresses).2.2 ≤ _
  exact hScan.trans (hPacked.trans hMono)

end Blotto.BinaryPRGHeapInitialLifetimeBound
