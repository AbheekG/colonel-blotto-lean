import Blotto.BinaryPRGWordControllerBooleanResourceLoopWork

/-! A native-resource source entry builds Boolean trees directly from incoming
array cells, initializes Boolean identifiers, runs the Boolean resource loop
and materializes only the final native continuation state. The proof-only
native views are never evaluated by the source runner. Boundary decoding and
array/list production have explicit prices; complete pointer-word/compiler
and lifetime interpretation remain separate. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceSource
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerWordStoreView BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourceLoop
variable {n : ℕ}

abbrev capacityStore (capacity : FixedArrayTable n SignedWord) : Store :=
  BinaryPRGWordControllerWordStore.prepare BinaryRationalOpcode.zero capacity.data.toList

abbrev resourceStore (capacity resource : FixedArrayTable n SignedWord) : Store :=
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  ⟨ruler.length,⟨ruler,rfl⟩,(build BinaryRationalOpcode.zero ruler resource.data.toList).1⟩

theorem source_count (capacity : FixedArrayTable n SignedWord) : n = (capacityStore capacity).cap.value := by
  unfold capacityStore
  rw [prepare_cap,Array.length_toList,capacity.size]

theorem arrayWords (table : FixedArrayTable n SignedWord) : List.ofFn table.read = table.data.toList := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,Array.length_toList,table.size]
  · intro i hi hj
    simp only [List.getElem_ofFn,Array.getElem_toList,FixedArrayTable.read]

theorem capacityStore_eq_ofTable (capacity : FixedArrayTable n SignedWord) : capacityStore capacity = ofTable capacity := by
  unfold capacityStore ofTable
  rw [arrayWords]

theorem capacityTable (capacity : FixedArrayTable n SignedWord) :
    table (capacityStore capacity).cap (capacityStore capacity).tree n (source_count capacity) = capacity := by
  change view (capacityStore capacity) n (source_count capacity) = capacity
  simpa only [capacityStore_eq_ofTable] using view_ofTable capacity

theorem resourceTable (capacity resource : FixedArrayTable n SignedWord) :
    table (capacityStore capacity).cap (resourceStore capacity resource).tree n (source_count capacity) = resource := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  change (view ⟨(capacityStore capacity).width,(capacityStore capacity).cap,(resourceStore capacity resource).tree⟩ n (source_count capacity)).read j = _
  rw [view_read]
  change lookup (build BinaryRationalOpcode.zero (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1
    (FixedBinaryWord.ofNat _ j.val) = resource.read j
  rw [build_lookup,FixedBinaryWord.value_ofNat]
  · rw [← arrayWords resource]
    simp [List.getD_eq_getElem?_getD,j.isLt]
  · have hRoom := cap_room (capacityStore capacity)
    rw [← source_count capacity] at hRoom
    exact j.isLt.trans hRoom

theorem capacityCanonical (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) :
    ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,
      CanonicalWord (lookup (capacityStore capacity).tree address.word) := by
  intro address
  have h := hC (address.index n (source_count capacity))
  have hRead := table_read (capacityStore capacity).tree address n (source_count capacity)
  have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n (source_count capacity))) (capacityTable capacity)
  exact (hTable.symm.trans hRead) ▸ h

theorem resourceCanonical (capacity resource : FixedArrayTable n SignedWord)
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,
      CanonicalWord (lookup (resourceStore capacity resource).tree address.word) := by
  intro address
  have h := hR (address.index n (source_count capacity))
  have hRead := table_read (resourceStore capacity resource).tree address n (source_count capacity)
  have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n (source_count capacity))) (resourceTable capacity resource)
  exact (hTable.symm.trans hRead) ▸ h

variable {capacity : Store} {hCount : n = capacity.cap.value}

def rowWords (capacity : Store) (state : State capacity.width capacity.cap) : List SignedWord :=
  (BinaryPRGWordControllerBooleanResourceInitial.allAddresses capacity).map (fun address => lookup state.resource address.word)

theorem rowWords_reference (capacity : Store) (state : State capacity.width capacity.cap)
    (n : ℕ) (hCount : n = capacity.cap.value) :
    rowWords capacity state = List.ofFn (table capacity.cap state.resource n hCount).read := by
  rw [List.ofFn_eq_map,← BinaryPRGWordControllerBooleanResourceInitial.allAddresses_indices capacity n hCount,List.map_map]
  unfold rowWords
  apply List.map_congr_left
  intro address _
  exact (table_read _ _ _ _).symm

def rowTable (capacity : Store) (state : State capacity.width capacity.cap)
    (n : ℕ) (hCount : n = capacity.cap.value) : FixedArrayTable n SignedWord :=
  ⟨(rowWords capacity state).toArray,by rw [List.size_toArray,rowWords_reference capacity state n hCount,List.length_ofFn]⟩

theorem rowTable_reference (capacity : Store) (state : State capacity.width capacity.cap)
    (n : ℕ) (hCount : n = capacity.cap.value) : rowTable capacity state n hCount = table capacity.cap state.resource n hCount := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  change (rowWords capacity state)[j.val]'_ = _
  simp only [rowWords_reference capacity state n hCount,List.getElem_ofFn]

def decodeIndex (address : Address capacity.width capacity.cap) (n : ℕ) (hCount : n = capacity.cap.value) : Fin n :=
  ⟨address.word.value,by simpa only [hCount] using address.in_cap⟩

def materializedState (state : Certified capacity n hCount) : BinaryResourceState.State n :=
  ⟨rowTable capacity state.state n hCount,state.state.active.map (fun address => decodeIndex address n hCount)⟩

theorem materializedState_reference (state : Certified capacity n hCount) :
    materializedState state = state.state.reference n hCount := by
  unfold materializedState State.reference
  rw [rowTable_reference]
  rfl

def materialize (state : Certified capacity n hCount) : BinaryResourcePair.Certified (table capacity.cap capacity.tree n hCount) :=
  { state := materializedState state
    canonical := by rw [materializedState_reference,← state.reference_state]; exact state.reference.canonical
    nodup := by rw [materializedState_reference,← state.reference_state]; exact state.reference.nodup
    membership := by rw [materializedState_reference,← state.reference_state]; exact state.reference.membership }

theorem materialize_reference (state : Certified capacity n hCount) : materialize state = state.reference := by
  apply native_ext
  rw [Certified.reference_state]
  exact materializedState_reference _

noncomputable def transport {first second : FixedArrayTable n SignedWord} (h : first = second)
    (state : BinaryResourcePair.Certified first) : BinaryResourcePair.Certified second := h ▸ state

theorem transport_state {first second : FixedArrayTable n SignedWord} (h : first = second)
    (state : BinaryResourcePair.Certified first) : (transport h state).state = state.state := by
  subst second
  rfl

def materializeTo (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity)
    (state : Certified capacity n hCount) : BinaryResourcePair.Certified nativeCapacity :=
  { state := materializedState state
    canonical := by rw [materializedState_reference,← state.reference_state]; exact state.reference.canonical
    nodup := by rw [materializedState_reference,← state.reference_state]; exact state.reference.nodup
    membership := by
      intro j
      have hm := state.reference.membership j
      have hc := congrArg (fun t : FixedArrayTable n SignedWord => t.read j) hTable
      rw [hc] at hm
      rw [materializedState_reference,← state.reference_state]
      exact hm }

theorem materializeTo_reference (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity)
    (state : Certified capacity n hCount) : materializeTo nativeCapacity hTable state = transport hTable state.reference := by
  apply native_ext
  rw [transport_state,Certified.reference_state]
  exact materializedState_reference _

def sourceMaterialize (capacity : FixedArrayTable n SignedWord)
    (state : Certified (capacityStore capacity) n (source_count capacity)) : BinaryResourcePair.Certified capacity :=
  { state := materializedState state
    canonical := by rw [materializedState_reference,← state.reference_state]; exact state.reference.canonical
    nodup := by rw [materializedState_reference,← state.reference_state]; exact state.reference.nodup
    membership := by
      intro j
      have hm := state.reference.membership j
      have hc := congrArg (fun t : FixedArrayTable n SignedWord => t.read j) (capacityTable capacity)
      rw [hc] at hm
      rw [materializedState_reference,← state.reference_state]
      exact hm }

theorem sourceMaterialize_reference (capacity : FixedArrayTable n SignedWord)
    (state : Certified (capacityStore capacity) n (source_count capacity)) :
    sourceMaterialize capacity state = transport (capacityTable capacity) state.reference := by
  apply native_ext
  rw [transport_state,Certified.reference_state]
  exact materializedState_reference _

def result (capacity : FixedArrayTable n SignedWord) (seed : BinarySeedLookupTree.Store)
    (drawn : Result seed (capacityStore capacity) n (source_count capacity)) :
    BinaryPRGWordControllerResource.Result seed capacity :=
  (drawn.1.map (sourceMaterialize capacity),drawn.2)

theorem result_reference (capacity : FixedArrayTable n SignedWord) (seed : BinarySeedLookupTree.Store)
    (drawn : Result seed (capacityStore capacity) n (source_count capacity)) :
    result capacity seed drawn = (drawn.original.1.map (transport (capacityTable capacity)),drawn.original.2) := by
  unfold result Result.original
  rw [Option.map_map]
  apply Prod.ext
  · apply congrArg (fun f => drawn.1.map f)
    funext state
    exact sourceMaterialize_reference capacity state
  · rfl

def initial (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    Certified (capacityStore capacity) n (source_count capacity) :=
  BinaryPRGWordControllerBooleanResourceLoop.initial (capacityStore capacity) (resourceStore capacity resource)
    rfl rfl n (source_count capacity) (capacityCanonical capacity hC) (resourceCanonical capacity resource hR)

theorem initial_reference (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    transport (capacityTable capacity) (initial capacity resource hC hR).reference =
      BinaryResourcePair.initial capacity resource hC hR := by
  apply native_ext
  rw [transport_state,Certified.reference_state]
  have h := BinaryPRGWordControllerBooleanResourceInitial.initial_reference
    (capacityStore capacity) (resourceStore capacity resource) rfl rfl n (source_count capacity)
  simp only [capacityTable] at h
  exact h.trans (congrArg (BinaryResourceState.initial capacity) (resourceTable capacity resource))

def initialRun (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerResource.Result seed capacity :=
  result capacity seed (BinaryPRGWordControllerBooleanResourceLoop.run seed (capacityStore capacity) n (source_count capacity)
    (capacityCanonical capacity hC) (initial capacity resource hC hR) (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _))

theorem run_transport (seed : BinarySeedLookupTree.Store) (first second : FixedArrayTable n SignedWord)
    (h : first = second) (hC : ∀ j,CanonicalWord (first.read j)) (hD : ∀ j,CanonicalWord (second.read j))
    (state : BinaryResourcePair.Certified first) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((BinaryPRGWordControllerResource.run seed first hC state pc hp).1.map (transport h),
      (BinaryPRGWordControllerResource.run seed first hC state pc hp).2) =
      BinaryPRGWordControllerResource.run seed second hD (transport h state) pc hp := by
  subst second
  change (Option.map id (BinaryPRGWordControllerResource.run seed first hC state pc hp).1,
    (BinaryPRGWordControllerResource.run seed first hC state pc hp).2) = _
  rw [Option.map_id]
  rfl

theorem initialRun_original (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    initialRun seed capacity resource hC hR = BinaryPRGWordControllerResource.initialRun seed capacity resource hC hR := by
  unfold initialRun
  rw [result_reference,BinaryPRGWordControllerBooleanResourceLoop.run_original,run_transport _ _ capacity _ _ hC]
  rw [initial_reference]
  rfl

end Blotto.BinaryPRGWordControllerBooleanResourceSource
