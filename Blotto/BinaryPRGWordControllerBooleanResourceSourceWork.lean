import Blotto.BinaryPRGWordControllerBooleanResourceSource

/-! Actual source conversion and Boolean resource execution are joined once.
Incoming native array cells build one cached capacity/resource tree pair;
Boolean initialization and the selected Boolean loop consume those trees.
Final row traversal, capped numeric index readback, list/array cells and
word copies have their own charges. No old numeric resource loop is run to
produce either the data or its cost. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceSourceWork
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerBooleanResourceUpdate BinaryPRGWordControllerBooleanResourceLoop
open BinaryPRGWordControllerBooleanResourceSource
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem table_data_ext {n : ℕ} (first second : FixedArrayTable n SignedWord) (h : first.data = second.data) : first = second := by
  cases first
  cases second
  cases h
  rfl

theorem state_ext (first second : BinaryResourceState.State n)
    (hr : first.resource = second.resource) (ha : first.active = second.active) : first = second := by
  cases first
  cases second
  cases hr
  cases ha
  rfl

def rowsWithWork {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (tree : Tree indexWidth) :
    List (Address indexWidth cap) → List SignedWord × ℕ
  | [] => ([],1)
  | address :: rest =>
      let word := lookup tree address.word
      let later := rowsWithWork tree rest
      (word :: later.1,lookupCells tree address.word + BinaryRationalExpression.payloadWords word + later.2 + 4)

theorem rowsWithWork_erasure {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (tree : Tree indexWidth)
    (addresses : List (Address indexWidth cap)) :
    (rowsWithWork tree addresses).1 = addresses.map (fun address => lookup tree address.word) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [rowsWithWork,List.map_cons,ih]

def rowsBound (indexWidth W count : ℕ) : ℕ := count * (10 * indexWidth + 4 * W + 12) + 1

theorem rowsWithWork_bound {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (tree : Tree indexWidth)
    (addresses : List (Address indexWidth cap)) (W : ℕ)
    (hW : ∀ address ∈ addresses,width (lookup tree address.word) ≤ W) :
    (rowsWithWork tree addresses).2 ≤ rowsBound indexWidth W addresses.length := by
  induction addresses with
  | nil => simp [rowsWithWork,rowsBound]
  | cons address rest ih =>
      have hc := BinaryRationalExpression.payloadWords_bound _ W (hW address (by simp))
      have hl := ih (fun next hn => hW next (by simp [hn]))
      unfold rowsWithWork rowsBound
      dsimp only
      rw [lookupCells_exact]
      simp only [List.length_cons]
      unfold rowsBound at hl
      nlinarith

def indicesWithWork {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value) :
    List (Address capacity.width capacity.cap) → List (Fin n) × ℕ
  | [] => ([],1)
  | address :: rest =>
      let later := indicesWithWork n hCount rest
      (decodeIndex address n hCount :: later.1,4 * (capacity.width + 1)^2 + later.2 + 4)

theorem indicesWithWork_erasure {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value)
    (addresses : List (Address capacity.width capacity.cap)) :
    (indicesWithWork n hCount addresses).1 = addresses.map (fun address => decodeIndex address n hCount) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [indicesWithWork,List.map_cons,ih]

theorem indicesWithWork_price {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value)
    (addresses : List (Address capacity.width capacity.cap)) :
    (indicesWithWork n hCount addresses).2 = addresses.length * (4 * (capacity.width + 1)^2 + 4) + 1 := by
  induction addresses with
  | nil => simp [indicesWithWork]
  | cons address rest ih => simp only [indicesWithWork,List.length_cons,ih]; ring

def materializeWithWork {capacity : Store} {hCount : n = capacity.cap.value}
    (nativeCapacity : FixedArrayTable n SignedWord) (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity)
    (state : Certified capacity n hCount) : BinaryResourcePair.Certified nativeCapacity × ℕ :=
  let enumerated := BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork capacity (zeroIndex capacity)
    (by rw [zeroIndex_value]; exact Nat.zero_le _)
  let rows := rowsWithWork state.state.resource enumerated.1
  let active := indicesWithWork n hCount state.state.active
  let nativeState : BinaryResourceState.State n :=
    ⟨⟨rows.1.toArray,by
      rw [List.size_toArray,rowsWithWork_erasure,BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork_erasure,
        List.length_map,BinaryPRGWordControllerBooleanResourceInitial.addresses_length,zeroIndex_value,Nat.sub_zero]
      exact hCount.symm⟩,active.1⟩
  have hState : nativeState = materializedState state := by
    apply state_ext
    · apply table_data_ext
      change rows.1.toArray = (rowWords capacity state.state).toArray
      dsimp only [rows]
      rw [rowsWithWork_erasure]
      dsimp only [enumerated]
      rw [BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork_erasure]
      rfl
    · exact indicesWithWork_erasure _ _ _
  (⟨nativeState,
      (by rw [hState]; exact (materializeTo nativeCapacity hTable state).canonical),
      (by rw [hState]; exact (materializeTo nativeCapacity hTable state).nodup),
      (by rw [hState]; exact (materializeTo nativeCapacity hTable state).membership)⟩,
    2 * capacity.width + 1 + enumerated.2 + rows.2 + active.2 + 3 * rows.1.length + 5)

theorem materializeWithWork_erasure {capacity : Store} {hCount : n = capacity.cap.value}
    (nativeCapacity : FixedArrayTable n SignedWord) (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity)
    (state : Certified capacity n hCount) :
    (materializeWithWork nativeCapacity hTable state).1 = materializeTo nativeCapacity hTable state := by
  apply native_ext
  apply state_ext
  · apply table_data_ext
    change (rowsWithWork state.state.resource
      (BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork capacity (zeroIndex capacity) _).1).1.toArray =
      (rowWords capacity state.state).toArray
    rw [rowsWithWork_erasure,BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork_erasure]
    rfl
  · exact indicesWithWork_erasure _ _ _

def outputBound (n indexWidth W : ℕ) : ℕ :=
  2 * indexWidth + 1 + BinaryPRGWordControllerBooleanResourceInitial.addressBound indexWidth n +
    rowsBound indexWidth W n + n * (4 * (indexWidth + 1)^2 + 4) + 1 + 3 * n + 5

theorem materializeWithWork_bound {capacity : Store} {hCount : n = capacity.cap.value}
    (nativeCapacity : FixedArrayTable n SignedWord) (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity)
    (state : Certified capacity n hCount) (W : ℕ)
    (hW : ∀ address : Address capacity.width capacity.cap,width (lookup state.state.resource address.word) ≤ W) :
    (materializeWithWork nativeCapacity hTable state).2 ≤ outputBound n capacity.width W := by
  have hEnumeration := BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork_bound capacity (zeroIndex capacity)
    (by rw [zeroIndex_value]; exact Nat.zero_le _)
  simp only [zeroIndex_value,Nat.sub_zero,← hCount] at hEnumeration
  let enumerated := BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork capacity (zeroIndex capacity)
    (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have hLength : enumerated.1.length = n := by
    dsimp only [enumerated]
    rw [BinaryPRGWordControllerBooleanResourceInitial.addressesWithWork_erasure,
      BinaryPRGWordControllerBooleanResourceInitial.addresses_length,zeroIndex_value,Nat.sub_zero]
    exact hCount.symm
  have hRows := rowsWithWork_bound state.state.resource enumerated.1 W (fun address _ => hW address)
  rw [hLength] at hRows
  have hActive := indicesWithWork_price n hCount state.state.active
  have hCountActive := BinaryGeneralResourceRun.active_length_le state.reference
  rw [state.reference_state] at hCountActive
  simp only [State.reference,List.length_map] at hCountActive
  have hRowLength : (rowsWithWork state.state.resource enumerated.1).1.length = n := by
    rw [rowsWithWork_erasure,List.length_map,hLength]
  unfold materializeWithWork outputBound
  dsimp only
  change 2 * capacity.width + 1 + enumerated.2 + (rowsWithWork state.state.resource enumerated.1).2 +
    (indicesWithWork n hCount state.state.active).2 + 3 * (rowsWithWork state.state.resource enumerated.1).1.length + 5 ≤ _
  rw [hActive,hRowLength]
  nlinarith

def inputWork (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  preparationCells BinaryRationalOpcode.zero capacity.data.toList +
    6 * buildVisits BinaryRationalOpcode.zero ruler resource.data.toList +
      copiedPayload (resourceStore capacity resource).tree + 6 * n + 7

def resourceFromCached (cached : Store) (items : List SignedWord) : Store :=
  ⟨cached.width,cached.cap,cached.cap.size ▸ (build BinaryRationalOpcode.zero cached.cap.bits items).1⟩

theorem resourceFromCached_source (capacity resource : FixedArrayTable n SignedWord) :
    resourceFromCached (capacityStore capacity) resource.data.toList = resourceStore capacity resource := rfl

def initialWithWork (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    Certified (capacityStore capacity) n (source_count capacity) × ℕ :=
  let cached := capacityStore capacity
  let resourceTree := resourceFromCached cached resource.data.toList
  let hWidth : resourceTree.width = cached.width := rfl
  let hCap : resourceTree.cap = hWidth.symm ▸ cached.cap := rfl
  let started := BinaryPRGWordControllerBooleanResourceInitial.initialWithWork cached resourceTree hWidth hCap
  (⟨started.1,by
      have he : started.1 = (initial capacity resource hC hR).state :=
        BinaryPRGWordControllerBooleanResourceInitial.initialWithWork_erasure cached resourceTree hWidth hCap
      exact he.symm ▸ (initial capacity resource hC hR).certified⟩,
    inputWork capacity resource + started.2)

theorem initialWithWork_erasure (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialWithWork capacity resource hC hR).1 = initial capacity resource hC hR := by
  apply BinaryPRGWordControllerBooleanResourceLoopWork.certified_ext
  change (BinaryPRGWordControllerBooleanResourceInitial.initialWithWork (capacityStore capacity) (resourceStore capacity resource) rfl rfl).1 =
    BinaryPRGWordControllerBooleanResourceInitial.initial (capacityStore capacity) (resourceStore capacity resource) rfl rfl
  exact BinaryPRGWordControllerBooleanResourceInitial.initialWithWork_erasure _ _ _ _

structure Prepared (nativeCapacity : FixedArrayTable n SignedWord) where
  cached : Store
  count : n = cached.cap.value
  table_correct : table cached.cap cached.tree n count = nativeCapacity
  canonical : ∀ address : Address cached.width cached.cap,CanonicalWord (lookup cached.tree address.word)
  state : Certified cached n count
  work : ℕ

def prepare (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) : Prepared capacity :=
  let cached := capacityStore capacity
  let resourceTree := resourceFromCached cached resource.data.toList
  let hWidth : resourceTree.width = cached.width := rfl
  let hCap : resourceTree.cap = hWidth.symm ▸ cached.cap := rfl
  let started := BinaryPRGWordControllerBooleanResourceInitial.initialWithWork cached resourceTree hWidth hCap
  { cached := cached
    count := source_count capacity
    table_correct := capacityTable capacity
    canonical := capacityCanonical capacity hC
    state := ⟨started.1,by
      have he : started.1 = (initial capacity resource hC hR).state :=
        BinaryPRGWordControllerBooleanResourceInitial.initialWithWork_erasure cached resourceTree hWidth hCap
      exact he.symm ▸ (initial capacity resource hC hR).certified⟩
    work := inputWork capacity resource + started.2 }

theorem prepare_state (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (prepare capacity resource hC hR).state = (initialWithWork capacity resource hC hR).1 := rfl

def initialRun (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerResource.Result seed capacity × ℕ :=
  let started := prepare capacity resource hC hR
  let drawn := BinaryPRGWordControllerBooleanResourceLoopWork.run seed started.cached n started.count
    started.canonical started.state (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  match drawn.1.1 with
  | none => ((none,drawn.1.2),started.work + 2 * seed.width + 1 + drawn.2 + 2)
  | some state =>
      let output := materializeWithWork capacity started.table_correct state
      ((some output.1,drawn.1.2),started.work + 2 * seed.width + 1 + drawn.2 + output.2 + 2)

theorem initialRun_erasure (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialRun seed capacity resource hC hR).1 = BinaryPRGWordControllerResource.initialRun seed capacity resource hC hR := by
  rw [← BinaryPRGWordControllerBooleanResourceSource.initialRun_original seed capacity resource hC hR]
  unfold initialRun BinaryPRGWordControllerBooleanResourceSource.initialRun result
  dsimp only
  rw [BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure,prepare_state,initialWithWork_erasure]
  dsimp only [prepare]
  cases hs : (BinaryPRGWordControllerBooleanResourceLoop.run seed (capacityStore capacity) n (source_count capacity)
      (capacityCanonical capacity hC) (initial capacity resource hC hR) (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).1 with
  | none => simp only [Option.map_none]
  | some state =>
      simp only [Option.map_some]
      apply Prod.ext
      · apply congrArg some
        exact materializeWithWork_erasure capacity (capacityTable capacity) state
      · rfl

open BinaryGeneralResourceLattice

def inputBound (n W : ℕ) : ℕ := 63 * n + 19 + 2 * (2 * n + 1) * (1 + 2 * W)

theorem inputWork_bound (capacity resource : FixedArrayTable n SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hC : ∀ j,width (capacity.read j) ≤ W) (hR : ∀ j,width (resource.read j) ≤ W) :
    inputWork capacity resource ≤ inputBound n W := by
  have hz : BinaryRationalExpression.payloadWords BinaryRationalOpcode.zero ≤ 1 + 2 * W := by
    change 2 ≤ 1 + 2 * W
    omega
  have capItems : ∀ word ∈ capacity.data.toList,BinaryRationalExpression.payloadWords word ≤ 1 + 2 * W := by
    intro word hm
    rw [← arrayWords capacity] at hm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
    exact BinaryRationalExpression.payloadWords_bound _ _ (hC j)
  have resItems : ∀ word ∈ resource.data.toList,BinaryRationalExpression.payloadWords word ≤ 1 + 2 * W := by
    intro word hm
    rw [← arrayWords resource] at hm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
    exact BinaryRationalExpression.payloadWords_bound _ _ (hR j)
  have hp := preparationCells_bound BinaryRationalOpcode.zero capacity.data.toList (1 + 2 * W) hz capItems
  simp only [Array.length_toList,capacity.size] at hp
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  have hv := buildVisits_exact BinaryRationalOpcode.zero ruler resource.data.toList
  have ht := prepare_capacity_bound BinaryRationalOpcode.zero capacity.data.toList
  simp only [Array.length_toList,capacity.size] at ht
  change 2^ruler.length ≤ 2 * n + 1 at ht
  rw [pow_succ] at hv
  have hm := build_maxPayload_bound BinaryRationalOpcode.zero ruler resource.data.toList (1 + 2 * W)
    (getD_payload_bound _ _ _ hz resItems)
  have hh := copiedPayload_bound (resourceStore capacity resource).tree
  have hCopy : copiedPayload (resourceStore capacity resource).tree ≤ (2 * n + 1) * (1 + 2 * W) :=
    hh.trans (Nat.mul_le_mul ht hm)
  unfold inputWork inputBound
  change preparationCells BinaryRationalOpcode.zero capacity.data.toList +
    6 * buildVisits BinaryRationalOpcode.zero ruler resource.data.toList +
      copiedPayload (resourceStore capacity resource).tree + 6 * n + 7 ≤ _
  nlinarith

def initialBound (n D resourceIndexWidth seedIndexWidth N : ℕ) : ℕ :=
  inputBound n (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
    BinaryPRGWordControllerBooleanResourceInitial.initialBound resourceIndexWidth
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) n + 2 * seedIndexWidth + 1 +
    BinaryPRGWordControllerBooleanResourceLoopWork.bound n D resourceIndexWidth seedIndexWidth n N +
      outputBound n resourceIndexWidth (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) + 2

def requestRun (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGWordControllerResource.Result seed (BinaryPRGResourceWork.resourceInput request rich).length × ℕ :=
  initialRun seed (BinaryPRGResourceWork.resourceInput request rich).length
    (BinaryPRGResourceWork.resourceInput request rich).resource
    (BinaryPRGResourceWork.resource_canonical request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request rich).2.2

theorem requestRun_erasure (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRun seed request rich).1 = BinaryPRGWordControllerResource.requestRun seed request rich :=
  initialRun_erasure _ _ _ _ _

theorem invariant_transport {first second : FixedArrayTable n SignedWord} (h : first = second)
    (D : ℕ) (state : BinaryResourcePair.Certified first) :
    StateInvariant second D (transport h state) = StateInvariant first D state := by
  subst second
  rfl

theorem initial_invariant (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ)
    (hLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) :
    StateInvariant (table (capacityStore capacity).cap (capacityStore capacity).tree n (source_count capacity)) D
      (initial capacity resource hC hR).reference := by
  rw [← invariant_transport (capacityTable capacity) D (initial capacity resource hC hR).reference,
    BinaryPRGWordControllerBooleanResourceSource.initial_reference]
  exact BinaryGeneralResourceLattice.initial_invariant capacity resource hC hR D hLattice hBox

theorem initialRun_bound (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) :
    (initialRun seed capacity resource hC hR).2 ≤
      initialBound n D (capacityStore capacity).width seed.width seed.cap.value := by
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  have hW : 1 ≤ W := by dsimp [W,BinaryPRGWordControllerBooleanResourceLoopWork.widthBound]; omega
  have hNative := BinaryGeneralResourceLattice.initial_invariant capacity resource hC hR D hResource hResourceBox
  have hcWidth : ∀ j,width (capacity.read j) ≤ W := by
    intro j
    have h := capacity_wordWidth capacity hC D hD hLattice hBox j
    dsimp [W,BinaryPRGWordControllerBooleanResourceLoopWork.widthBound]
    omega
  have hrWidth : ∀ j,width (resource.read j) ≤ W := by
    intro j
    have h := state_wordWidth (BinaryResourcePair.initial capacity resource hC hR) D hD (fun j => (hBox j).2) hNative j
    change width (resource.read j) ≤ _ at h
    dsimp [W,BinaryPRGWordControllerBooleanResourceLoopWork.widthBound]
    omega
  have hInput := inputWork_bound capacity resource W hW hcWidth hrWidth
  have hCapTree : ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,
      width (lookup (capacityStore capacity).tree address.word) ≤ W := by
    intro address
    have hRead := table_read (capacityStore capacity).tree address n (source_count capacity)
    have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n (source_count capacity))) (capacityTable capacity)
    rw [← hRead,hTable]
    exact hcWidth _
  have hResTree : ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,
      width (lookup (resourceStore capacity resource).tree address.word) ≤ W := by
    intro address
    have hRead := table_read (resourceStore capacity resource).tree address n (source_count capacity)
    have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n (source_count capacity))) (resourceTable capacity resource)
    exact (hTable.symm.trans hRead) ▸ hrWidth (address.index n (source_count capacity))
  have hStart := BinaryPRGWordControllerBooleanResourceInitial.initialWithWork_bound
    (capacityStore capacity) (resourceStore capacity resource) rfl rfl W hW hCapTree hResTree
  rw [← source_count capacity] at hStart
  let started := prepare capacity resource hC hR
  have hPreparedWork : started.work ≤ inputBound n W +
      BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W n :=
    Nat.add_le_add hInput hStart
  have hLatticeTree : ∀ j,OnRationalLattice D
      (value ((table (capacityStore capacity).cap (capacityStore capacity).tree n (source_count capacity)).read j)) := by
    intro j
    rw [capacityTable]
    exact hLattice j
  have hBoxTree : ∀ j,0 ≤ value ((table (capacityStore capacity).cap (capacityStore capacity).tree n (source_count capacity)).read j) ∧
      value ((table (capacityStore capacity).cap (capacityStore capacity).tree n (source_count capacity)).read j) ≤ 1 := by
    intro j
    rw [capacityTable]
    exact hBox j
  have hs : StateInvariant (table started.cached.cap started.cached.tree n started.count) D started.state.reference := by
    rw [prepare_state,initialWithWork_erasure]
    exact initial_invariant capacity resource hC hR D hResource hResourceBox
  have hRun := BinaryPRGWordControllerBooleanResourceLoopWork.run_bound D hD seed started.cached n started.count started.canonical started.state
    hLatticeTree hBoxTree hs (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hActive := BinaryGeneralResourceRun.active_length_le started.state.reference
  rw [Certified.reference_state] at hActive
  simp only [State.reference,List.length_map] at hActive
  have hPosition := BinaryPRGWordControllerBooleanResourceLoop.run_position seed started.cached n started.count started.canonical started.state
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  rw [← BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure] at hPosition
  simp only [BinaryWordIndexCoinController.zeroIndex_value,Nat.sub_zero] at hRun
  have hRunCap : (BinaryPRGWordControllerBooleanResourceLoopWork.run seed started.cached n started.count started.canonical started.state
      (BinaryWordIndexCoinController.zeroIndex seed) (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2 ≤
      BinaryPRGWordControllerBooleanResourceLoopWork.bound n D started.cached.width seed.width n seed.cap.value := by
    apply hRun.trans
    unfold BinaryPRGWordControllerBooleanResourceLoopWork.bound
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1)) (Nat.mul_le_mul_right _ hPosition.2)
  unfold initialRun
  dsimp only
  change (match (BinaryPRGWordControllerBooleanResourceLoopWork.run seed started.cached n started.count started.canonical started.state
      (BinaryWordIndexCoinController.zeroIndex seed) _).1.1 with
    | none => ((none,_),started.work + 2 * seed.width + 1 + _ + 2)
    | some state => ((some _,_),started.work + 2 * seed.width + 1 + _ + _ + 2)).2 ≤ _
  split
  · unfold initialBound
    change started.work + 2 * seed.width + 1 + _ + 2 ≤
      inputBound n W + BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W n +
        2 * seed.width + 1 + BinaryPRGWordControllerBooleanResourceLoopWork.bound n D started.cached.width seed.width n seed.cap.value +
          outputBound n started.cached.width W + 2
    dsimp only [started] at hRunCap hPreparedWork ⊢
    omega
  · rename_i finished hSuccess
    have hFinal := BinaryPRGWordControllerBooleanResourceLoopWork.run_completed_invariant D seed started.cached n started.count started.canonical
      started.state hLatticeTree hs (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _) finished hSuccess
    have hOutput := materializeWithWork_bound capacity started.table_correct finished W
      (BinaryPRGWordControllerBooleanResourceLoopWork.state_width D hD finished (fun j => (hBoxTree j).2) hFinal)
    unfold initialBound
    change started.work + 2 * seed.width + 1 + _ + (materializeWithWork capacity started.table_correct finished).2 + 2 ≤
      inputBound n W + BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W n +
        2 * seed.width + 1 + BinaryPRGWordControllerBooleanResourceLoopWork.bound n D started.cached.width seed.width n seed.cap.value +
          outputBound n started.cached.width W + 2
    dsimp only [started] at hRunCap hPreparedWork hOutput ⊢
    omega

theorem initialBound_mono {n D resourceIndexWidth otherWidth seedIndexWidth N : ℕ}
    (h : resourceIndexWidth ≤ otherWidth) : initialBound n D resourceIndexWidth seedIndexWidth N ≤ initialBound n D otherWidth seedIndexWidth N := by
  simp only [initialBound,BinaryPRGWordControllerBooleanResourceInitial.initialBound,BinaryPRGWordControllerBooleanResourceInitial.addressBound,
    BinaryPRGWordControllerBooleanResourceUpdateWork.fractionalBound,BinaryPRGWordControllerBooleanResourceLoopWork.bound,
    BinaryPRGWordControllerBooleanResourceLoopWork.pairBound,BinaryPRGWordControllerBooleanResourcePair.bound,
    BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound,outputBound,rowsBound]
  gcongr

theorem resourceIndex_bound (capacity : FixedArrayTable n SignedWord) : (capacityStore capacity).width ≤ n + 1 := by
  have h := prepare_width_bound BinaryRationalOpcode.zero capacity.data.toList
  simp only [Array.length_toList,capacity.size] at h
  have hl := Nat.log2_le_self n
  exact h.trans (by unfold binaryWordWidth; omega)

theorem initialRun_dimension_bound (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) :
    (initialRun seed capacity resource hC hR).2 ≤ initialBound n D (n + 1) seed.width seed.cap.value :=
  (initialRun_bound D hD seed capacity resource hC hR hLattice hResource hBox hResourceBox).trans
    (initialBound_mono (resourceIndex_bound capacity))

theorem requestRun_bound (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRun seed request rich).2 ≤ initialBound n request.source.normalizedInput.latticeDenominator (n + 1) seed.width seed.cap.value := by
  obtain ⟨hL,hR,hBox,hResourceBox⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  exact initialRun_dimension_bound _ request.source.normalizedInput.latticeDenominator_pos _ _ _ _ _ hL hR hBox hResourceBox

def initialAt (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed capacity × ℕ :=
  let started := prepare capacity resource hC hR
  let drawn := BinaryPRGWordControllerBooleanResourceLoopWork.run seed started.cached n started.count
    started.canonical started.state pc hp
  match drawn.1.1 with
  | none => ((none,drawn.1.2),started.work + drawn.2 + 2)
  | some state =>
      let output := materializeWithWork capacity started.table_correct state
      ((some output.1,drawn.1.2),started.work + drawn.2 + output.2 + 2)

theorem initialAt_erasure (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (initialAt seed capacity resource hC hR pc hp).1 =
      BinaryPRGWordControllerResource.run seed capacity hC (BinaryResourcePair.initial capacity resource hC hR) pc hp := by
  have h : result capacity seed (BinaryPRGWordControllerBooleanResourceLoop.run seed (capacityStore capacity) n (source_count capacity)
      (capacityCanonical capacity hC) (initial capacity resource hC hR) pc hp) =
      BinaryPRGWordControllerResource.run seed capacity hC (BinaryResourcePair.initial capacity resource hC hR) pc hp := by
    rw [result_reference,BinaryPRGWordControllerBooleanResourceLoop.run_original,run_transport _ _ capacity _ _ hC]
    rw [BinaryPRGWordControllerBooleanResourceSource.initial_reference]
  rw [← h]
  unfold initialAt result
  dsimp only
  rw [BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure,prepare_state,initialWithWork_erasure]
  dsimp only [prepare]
  cases hs : (BinaryPRGWordControllerBooleanResourceLoop.run seed (capacityStore capacity) n (source_count capacity)
      (capacityCanonical capacity hC) (initial capacity resource hC hR) pc hp).1 with
  | none => simp only [Option.map_none]
  | some state =>
      simp only [Option.map_some]
      apply Prod.ext
      · apply congrArg some
        exact materializeWithWork_erasure capacity (capacityTable capacity) state
      · rfl

end Blotto.BinaryPRGWordControllerBooleanResourceSourceWork
