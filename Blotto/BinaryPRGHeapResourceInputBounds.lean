import Blotto.BinaryPRGHeapResourceSourceReservation

/-! Original array word widths bound the actual initial physical heaps and
their preparation. No reached heap or tree-cost oracle is supplied. -/

namespace Blotto.BinaryPRGHeapResourceInputBounds
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapPackedStore (pack)

theorem prepareRuler_heap_bound (fallback : SignedWord) (ruler : List Bool)
    (items : List SignedWord) :
    (BinaryPRGHeapStoredTree.prepareRulerWithWork fallback ruler items).1.heap.tape.length ≤
      BinaryPRGWordStoreHeap.heapBound (BinaryPRGWordStoreHeap.rawSize fallback ruler items) := by
  let N := BinaryPRGWordStoreHeap.rawSize fallback ruler items
  have hProduct : N * (4 * (N + 10) + 5) ≤ BinaryPRGWordStoreHeap.heapBound N := by
    unfold BinaryPRGWordStoreHeap.heapBound; nlinarith
  have hRoom : BinaryPRGWordStoreHeap.empty.tape.length + N * (4 * (N + 10) + 5) <
      2^(N + 10) := by
    simpa only [BinaryPRGWordStoreHeap.empty,List.length_nil,Nat.zero_add] using
      hProduct.trans_lt (BinaryPRGWordStoreHeap.quadratic_lt_capacity N)
  have h := BinaryPRGWordStoreHeap.build_size fallback ruler items
    BinaryPRGWordStoreHeap.empty BinaryPRGWordStoreHeap.empty_valid
    (N + 10) (by omega) hRoom
  simp only [BinaryPRGWordStoreHeap.empty,List.length_nil,Nat.zero_add] at h
  unfold BinaryPRGHeapStoredTree.prepareRulerWithWork
  dsimp only
  rw [BinaryPRGWordStoreHeapMachine.buildWithWork_erasure]
  exact h.trans hProduct

def initialHeapBound (count W : ℕ) : ℕ :=
  BinaryPRGWordStoreHeap.heapBound ((2 * count + 1) * (2 * W + 2))

variable {n : ℕ}

theorem array_member_width (input : FixedArrayTable n SignedWord) (W : ℕ)
    (hW : ∀ j,width (input.read j) ≤ W) :
    ∀ word ∈ input.data.toList,width word ≤ W := by
  rw [← BinaryPRGWordControllerBooleanResourceSource.arrayWords]
  intro word h
  rcases List.mem_ofFn.mp h with ⟨j,rfl⟩
  exact hW j

theorem prepared_heap_bound (capacity input : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W) (hInput : ∀ j,width (input.read j) ≤ W) :
    (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
      (BinaryCarryCounter.count capacity.data.toList []) input.data.toList).1.heap.tape.length ≤
      initialHeapBound n W := by
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  have hFallback : BinaryRationalExpression.payloadWords BinaryRationalOpcode.zero ≤ 1 + 2 * W := by
    change 2 ≤ 1 + 2 * W; omega
  have hItems : ∀ word ∈ input.data.toList,
      BinaryRationalExpression.payloadWords word ≤ 1 + 2 * W := by
    intro word hm
    have hw := array_member_width input W hInput word hm
    have hn := (Nat.le_max_left _ _).trans hw
    have hd := (Nat.le_max_right _ _).trans hw
    unfold BinaryRationalExpression.payloadWords
    omega
  have hMax := BinaryPRGWordControllerWordStore.build_maxPayload_bound
    BinaryRationalOpcode.zero ruler input.data.toList (1 + 2 * W)
    (BinaryPRGWordControllerWordStore.getD_payload_bound _ _ _ hFallback hItems)
  have hRaw := BinaryPRGWordStoreHeap.rawTreeSize_bound
    (BinaryPRGWordControllerWordStore.build BinaryRationalOpcode.zero ruler input.data.toList).1
  have hCapacity := BinaryPRGWordControllerWordStore.prepare_capacity_bound
    BinaryRationalOpcode.zero capacity.data.toList
  change 2^ruler.length ≤ 2 * capacity.data.toList.length + 1 at hCapacity
  simp only [Array.length_toList,capacity.size] at hCapacity
  have hRawBound := hRaw.trans
    (Nat.mul_le_mul hCapacity (Nat.add_le_add_right hMax 1))
  rw [← BinaryPRGWordStoreHeap.rawSize_build] at hRawBound
  rw [show 1 + 2 * W + 1 = 2 * W + 2 by omega] at hRawBound
  have hRaw' : BinaryPRGWordStoreHeap.rawSize BinaryRationalOpcode.zero ruler input.data.toList ≤
      (2 * n + 1) * (2 * W + 2) := by omega
  exact (prepareRuler_heap_bound _ _ _).trans
    (BinaryPRGWordStoreHeap.heapBound_mono hRaw')

theorem initial_heaps_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1.heap.tape.length ≤
        initialHeapBound n W ∧
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.2.heap.tape.length ≤
        initialHeapBound n W := by
  exact ⟨prepared_heap_bound capacity capacity W hW hCapacity,
    prepared_heap_bound capacity resource W hW hResource⟩

theorem source_depth (capacity : FixedArrayTable n SignedWord) :
    (BinaryPRGHeapResourceSource.capStore capacity).width ≤ binaryWordWidth n := by
  have h := BinaryPRGWordControllerWordStore.prepare_width_bound
    BinaryRationalOpcode.zero capacity.data.toList
  simpa only [Array.length_toList,capacity.size] using h

theorem source_nodes (capacity : FixedArrayTable n SignedWord) :
    BinaryPRGWordStoreHeapMachine.nodes
      (BinaryCarryCounter.count capacity.data.toList []).length ≤ 4 * n + 1 := by
  have h := BinaryPRGWordControllerWordStore.prepare_capacity_bound
    BinaryRationalOpcode.zero capacity.data.toList
  change 2^(BinaryCarryCounter.count capacity.data.toList []).length ≤
    2 * capacity.data.toList.length + 1 at h
  simp only [Array.length_toList,capacity.size] at h
  unfold BinaryPRGWordStoreHeapMachine.nodes
  rw [pow_succ]
  omega

theorem readBound_mono {a b i j : ℕ} (hCells : a ≤ b) (hDepth : i ≤ j) :
    BinaryPRGHeapStoredTree.readBound a i ≤ BinaryPRGHeapStoredTree.readBound b j := by
  have h := BinaryPRGWordStoreHeapMachine.lookupBound_mono hCells hDepth
  unfold BinaryPRGHeapStoredTree.readBound
  omega

theorem scanBound_mono {C H depth C' H' depth' W count : ℕ}
    (hC : C ≤ C') (hH : H ≤ H') (hDepth : depth ≤ depth') :
    BinaryPRGHeapResourceUpdateBudget.scanBound C H depth W count ≤
      BinaryPRGHeapResourceUpdateBudget.scanBound C' H' depth' W count := by
  have hc := readBound_mono hC hDepth
  have hh := readBound_mono hH hDepth
  have hStep : BinaryPRGHeapResourceUpdateBudget.testBound C H depth W +
      2 * (depth + 1) + 3 ≤
      BinaryPRGHeapResourceUpdateBudget.testBound C' H' depth' W +
        2 * (depth' + 1) + 3 := by
    unfold BinaryPRGHeapResourceUpdateBudget.testBound
    omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left count hStep) 1

theorem prepared_read_width (capacity input : FixedArrayTable n SignedWord)
    (W : ℕ) (hInput : ∀ j,width (input.read j) ≤ W)
    (address : Address (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap) :
    width (BinaryPRGHeapStoredTree.readWithWork
      (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
        (BinaryCarryCounter.count capacity.data.toList []) input.data.toList).1 address.word).1 ≤ W := by
  have hRead := BinaryPRGHeapStoredTree.readWithWork_value
    (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
      (BinaryCarryCounter.count capacity.data.toList []) input.data.toList).1 address.word
  have h := hInput (address.index n (BinaryPRGHeapResourceSource.count capacity))
  rw [← BinaryPRGWordControllerBooleanResourceSource.resourceTable capacity input] at h
  have hTable := BinaryPRGWordControllerBooleanResourceUpdate.table_read
    (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity input).tree
    address n (BinaryPRGHeapResourceSource.count capacity)
  exact (congrArg width hRead).trans_le ((congrArg width hTable).symm.trans_le h)

def preparationBound (count W : ℕ) : ℕ :=
  let depth := binaryWordWidth count
  let K := initialHeapBound count W
  2 * count + 2 * (4 * count + 1) * (BinaryPRGWordStoreHeapMachine.allocationBound K + 8) +
    count * (20 * (depth + 1) + 4) + 12 * (depth + 1) + 1 +
    BinaryPRGHeapResourceUpdateBudget.scanBound K K depth W count + 8

/-- The count, address enumeration, and scan allowance after the two physical
tree builds have been charged separately. -/
def preparationResidualBound (count W : ℕ) : ℕ :=
  let depth := binaryWordWidth count
  let K := initialHeapBound count W
  2 * count +
    count * (20 * (depth + 1) + 4) + 12 * (depth + 1) + 1 +
    BinaryPRGHeapResourceUpdateBudget.scanBound K K depth W count + 8

theorem preparationBound_split (count W : ℕ) :
    preparationBound count W =
      2 * (4 * count + 1) *
        (BinaryPRGWordStoreHeapMachine.allocationBound (initialHeapBound count W) + 8) +
      preparationResidualBound count W := by
  dsimp [preparationBound,preparationResidualBound]
  omega

theorem fractionalWorkBoundPacked_bound {depth : ℕ} {cap : FixedBinaryWord depth}
    (limits bids : BinaryPRGHeapPackedStore.Packed depth) (address : Address depth cap)
    (C H W : ℕ) (hC : limits.heap.tape.length ≤ C) (hH : bids.heap.tape.length ≤ H)
    (hW : 1 ≤ W) (hBid : width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : width (limits.readWithWork address.word).1 ≤ W) :
    BinaryPRGHeapResourceLoop.fractionalWorkBoundPacked limits bids address ≤
      BinaryPRGHeapResourceUpdateBudget.testBound C H depth W := by
  have hb := readBound_mono hH (le_refl depth)
  have hc := readBound_mono hC (le_refl depth)
  have hw0 : BinaryRationalArithmetic.pairWidth
      (bids.readWithWork address.word).1 BinaryRationalOpcode.zero ≤ W :=
    max_le hBid (by change 1 ≤ W; exact hW)
  have hw1 : BinaryRationalArithmetic.pairWidth
      (limits.readWithWork address.word).1 (bids.readWithWork address.word).1 ≤ W :=
    max_le hLimit hBid
  have hp0 := Nat.pow_le_pow_left (Nat.add_le_add_right hw0 1) 2
  have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hw1 1) 2
  unfold BinaryPRGHeapResourceLoop.fractionalWorkBoundPacked
    BinaryPRGHeapResourceUpdateBudget.testBound
  dsimp only
  rw [address.word.size]
  omega

theorem scanWorkBoundPacked_bound {depth : ℕ} {cap : FixedBinaryWord depth}
    (limits bids : BinaryPRGHeapPackedStore.Packed depth) (addresses : List (Address depth cap))
    (C H W : ℕ) (hC : limits.heap.tape.length ≤ C) (hH : bids.heap.tape.length ≤ H)
    (hW : 1 ≤ W)
    (hBid : ∀ address : Address depth cap,width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address : Address depth cap,width (limits.readWithWork address.word).1 ≤ W) :
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked limits bids addresses ≤
      BinaryPRGHeapResourceUpdateBudget.scanBound C H depth W addresses.length := by
  induction addresses with
  | nil => simp [BinaryPRGHeapResourceLoop.scanWorkBoundPacked,
      BinaryPRGHeapResourceUpdateBudget.scanBound]
  | cons address rest ih =>
      have hf := fractionalWorkBoundPacked_bound limits bids address C H W hC hH hW
        (hBid address) (hLimit address)
      simp only [BinaryPRGHeapResourceLoop.scanWorkBoundPacked,List.map_cons,List.sum_cons] at *
      unfold BinaryPRGHeapResourceUpdateBudget.scanBound at *
      rw [address.word.size]
      simp only [List.length_cons]
      nlinarith

theorem initialWorkEnvelope_input_bound (capacity resource : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource ≤
      preparationBound n W := by
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let limits := BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler capacity.data.toList
  let bids := BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler resource.data.toList
  let capWord : FixedBinaryWord ruler.length := ⟨ruler,rfl⟩
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  let K := initialHeapBound n W
  have hc : limits.1.heap.tape.length ≤ K := prepared_heap_bound capacity capacity W hW hCapacity
  have hr : bids.1.heap.tape.length ≤ K := prepared_heap_bound capacity resource W hW hResource
  have hn := source_nodes capacity
  have hd := source_depth capacity
  change ruler.length ≤ binaryWordWidth n at hd
  have hAllocC : BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length ≤
      BinaryPRGWordStoreHeapMachine.allocationBound K := by
    unfold BinaryPRGWordStoreHeapMachine.allocationBound; gcongr
  have hAllocR : BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length ≤
      BinaryPRGWordStoreHeapMachine.allocationBound K := by
    unfold BinaryPRGWordStoreHeapMachine.allocationBound; gcongr
  have hLimits' := Nat.mul_le_mul hn (Nat.add_le_add_right hAllocC 8)
  have hBids' := Nat.mul_le_mul hn (Nat.add_le_add_right hAllocR 8)
  have hCap : capWord.value = n := (BinaryPRGHeapResourceSource.count capacity).symm
  have hIds' : n * (20 * (ruler.length + 1) + 4) + 12 * (ruler.length + 1) + 1 ≤
      n * (20 * (binaryWordWidth n + 1) + 4) +
      12 * (binaryWordWidth n + 1) + 1 := by
    gcongr
  have hLength : ids.1.length = n := by
    have hAll := BinaryPRGHeapAddressEnumeration.allWithWork_reference
      (BinaryPRGHeapResourceSource.capStore capacity)
    change ids.1 = _ at hAll
    have hv := congrArg List.length
      (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
        (BinaryPRGHeapResourceSource.capStore capacity))
    simp only [List.length_map,List.length_range] at hv
    exact (congrArg List.length hAll).trans
      (hv.trans (BinaryPRGHeapResourceSource.count capacity).symm)
  have hLimitWidth : ∀ address : Address (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits.1 address.word).1 ≤ W :=
    prepared_read_width capacity capacity W hCapacity
  have hBidWidth : ∀ address : Address (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((pack bids.1).readWithWork address.word).1 ≤ W :=
    prepared_read_width capacity resource W hResource
  have hScan := scanWorkBoundPacked_bound
    (pack limits.1) (pack bids.1) ids.1 K K W hc hr hW hBidWidth hLimitWidth
  have hScanLength := hScan.trans_eq (congrArg
    (fun count => BinaryPRGHeapResourceUpdateBudget.scanBound K K
      (BinaryPRGHeapResourceSource.capStore capacity).width W count) hLength)
  have hScan' := hScanLength.trans (scanBound_mono le_rfl le_rfl hd)
  have hCarry := BinaryCarryCounter.countCarryCells_bound capacity.data.toList []
  simp only [BinaryCarryCounter.ones,Array.length_toList,capacity.size,Nat.add_zero] at hCarry
  unfold BinaryPRGHeapResourceSource.initialWorkEnvelope
  dsimp only
  change BinaryCarryCounter.countCarryCells capacity.data.toList [] +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length + 8) +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length + 8) +
    capWord.value * (20 * (ruler.length + 1) + 4) + 12 * (ruler.length + 1) + 1 +
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked (pack limits.1) (pack bids.1) ids.1 + 8 ≤ _
  rw [hCap]
  unfold preparationBound
  change _ ≤ 2 * n + 2 * (4 * n + 1) * (BinaryPRGWordStoreHeapMachine.allocationBound K + 8) +
    n * (20 * (binaryWordWidth n + 1) + 4) + 12 * (binaryWordWidth n + 1) + 1 +
    BinaryPRGHeapResourceUpdateBudget.scanBound K K (binaryWordWidth n) W n + 8
  nlinarith

theorem initialWithWork_input_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 ≤
      preparationBound n W :=
  (BinaryPRGHeapResourceSource.initialWithWork_bound capacity resource hC hR).trans
    (initialWorkEnvelope_input_bound capacity resource W hW hCapacity hResource)

/-- The native initializer's non-builder work fits the residual allowance.
The two native builder charges remain explicit so that a physical build can
replace them without paying the conservative builder bound again. -/
theorem initialWithWork_le_nativeBuild_plus_residual
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    let ruler := BinaryCarryCounter.count capacity.data.toList []
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 ≤
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero ruler capacity.data.toList).2.work +
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero ruler resource.data.toList).2.work +
      preparationResidualBound n W := by
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let limits := BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler capacity.data.toList
  let bids := BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler resource.data.toList
  let capWord : FixedBinaryWord ruler.length := ⟨ruler,rfl⟩
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  let K := initialHeapBound n W
  have hc : limits.1.heap.tape.length ≤ K := prepared_heap_bound capacity capacity W hW hCapacity
  have hr : bids.1.heap.tape.length ≤ K := prepared_heap_bound capacity resource W hW hResource
  have hd := source_depth capacity
  change ruler.length ≤ binaryWordWidth n at hd
  have hCap : capWord.value = n := (BinaryPRGHeapResourceSource.count capacity).symm
  have hIds := BinaryPRGHeapAddressEnumeration.allWithWork_bound capWord
  have hIds' : ids.2 ≤
      n * (20 * (binaryWordWidth n + 1) + 4) +
      12 * (binaryWordWidth n + 1) + 1 := by
    change ids.2 ≤ capWord.value * (20 * (ruler.length + 1) + 4) +
      12 * (ruler.length + 1) + 1 at hIds
    rw [hCap] at hIds
    have hMono : n * (20 * (ruler.length + 1) + 4) +
        12 * (ruler.length + 1) + 1 ≤
        n * (20 * (binaryWordWidth n + 1) + 4) +
        12 * (binaryWordWidth n + 1) + 1 := by gcongr
    exact hIds.trans hMono
  have hLength : ids.1.length = n := by
    have hAll := BinaryPRGHeapAddressEnumeration.allWithWork_reference
      (BinaryPRGHeapResourceSource.capStore capacity)
    change ids.1 = _ at hAll
    have hv := congrArg List.length
      (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values
        (BinaryPRGHeapResourceSource.capStore capacity))
    simp only [List.length_map,List.length_range] at hv
    exact (congrArg List.length hAll).trans
      (hv.trans (BinaryPRGHeapResourceSource.count capacity).symm)
  have hLimitWidth : ∀ address : Address (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits.1 address.word).1 ≤ W :=
    prepared_read_width capacity capacity W hCapacity
  have hBidWidth : ∀ address : Address (BinaryPRGHeapResourceSource.capStore capacity).width
      (BinaryPRGHeapResourceSource.capStore capacity).cap,
      width ((pack bids.1).readWithWork address.word).1 ≤ W :=
    prepared_read_width capacity resource W hResource
  have hScan := scanWorkBoundPacked_bound
    (pack limits.1) (pack bids.1) ids.1 K K W hc hr hW hBidWidth hLimitWidth
  have hScanLength := hScan.trans_eq (congrArg
    (fun count => BinaryPRGHeapResourceUpdateBudget.scanBound K K
      (BinaryPRGHeapResourceSource.capStore capacity).width W count) hLength)
  have hScan' := hScanLength.trans (scanBound_mono le_rfl le_rfl hd)
  have hScanNative := BinaryPRGHeapResourceLoop.scanWithWork_bound
    (capacity := BinaryPRGHeapResourceSource.capStore capacity)
    limits.1 (pack bids.1) ids.1
  change (BinaryPRGHeapResourceLoop.scanWithWork (capacity :=
    BinaryPRGHeapResourceSource.capStore capacity)
    limits.1 (pack bids.1) ids.1).2 ≤
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked
      (pack limits.1) (pack bids.1) ids.1 at hScanNative
  have hCarry := BinaryCarryCounter.countCarryCells_bound capacity.data.toList []
  simp only [BinaryCarryCounter.ones,Array.length_toList,capacity.size,Nat.add_zero] at hCarry
  unfold BinaryPRGHeapResourceSource.initialWithWork
  dsimp only
  change BinaryCarryCounter.countCarryCells capacity.data.toList [] +
    limits.2.work + bids.2.work + ids.2 +
    (BinaryPRGHeapResourceLoop.scanWithWork (capacity :=
      BinaryPRGHeapResourceSource.capStore capacity)
      limits.1 (pack bids.1) ids.1).2 + 8 ≤ _
  unfold preparationResidualBound
  change _ ≤ limits.2.work + bids.2.work +
    (2*n + n * (20 * (binaryWordWidth n + 1) + 4) +
      12 * (binaryWordWidth n + 1) + 1 +
      BinaryPRGHeapResourceUpdateBudget.scanBound K K (binaryWordWidth n) W n + 8)
  omega

end Blotto.BinaryPRGHeapResourceInputBounds
