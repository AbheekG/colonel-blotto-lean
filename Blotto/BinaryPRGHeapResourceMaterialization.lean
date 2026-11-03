import Blotto.BinaryPRGHeapResourceSource

/-! Read a terminal heap through physical tape lookups and assemble the native
resource row. The logical resource tree appears only in refinement proofs. -/

namespace Blotto.BinaryPRGHeapResourceMaterialization
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGWordControllerBooleanResourceLoop (Certified)

variable {width : ℕ} {cap : FixedBinaryWord width}

def collectWithWork (bids : Packed width) :
    List (Address width cap) → List SignedWord × ℕ
  | [] => ([],1)
  | address :: rest =>
      let found := bids.readWithWork address.word
      let later := collectWithWork bids rest
      (found.1 :: later.1,found.2.work + later.2 + 2 * (address.word.bits.length + 1) + 3)

theorem collectWithWork_reference (bids : Packed width)
    {tree : BinaryPRGWordControllerWordStore.Tree width}
    (h : BinaryPRGWordStoreHeap.Realizes bids.heap.tape bids.root tree)
    (ids : List (Address width cap)) :
    (collectWithWork bids ids).1 = ids.map (fun address => lookup tree address.word) := by
  induction ids with
  | nil => rfl
  | cons address rest ih =>
      simp only [collectWithWork,List.map_cons,
        BinaryPRGHeapPackedStore.Packed.readWithWork_value bids h address.word,ih]

theorem packedReadWorkBound (bids : Packed width) (address : FixedBinaryWord width) :
    (bids.readWithWork address).2.work ≤
      BinaryPRGHeapStoredTree.readBound bids.heap.tape.length width :=
  bids.readWithWork_bounds address

theorem collectWithWork_bound (bids : Packed width) (ids : List (Address width cap)) :
    (collectWithWork bids ids).2 ≤
      ids.length * (BinaryPRGHeapStoredTree.readBound bids.heap.tape.length width +
        2 * (width + 1) + 3) + 1 := by
  induction ids with
  | nil => simp only [collectWithWork,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons address rest ih =>
      have hRead := bids.readWithWork_bounds address.word
      simp only [collectWithWork,List.length_cons]
      rw [address.word.size]
      rw [Nat.add_mul]
      simp only [one_mul]
      omega

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def rowWordsWithWork (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) : List SignedWord × ℕ :=
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  let addresses : List (Address capacity.width capacity.cap) := hCap ▸ ids.1
  let rows := collectWithWork state.packed addresses
  (rows.1,ids.2 + rows.2 + 3)

theorem rowWordsWithWork_reference (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowWordsWithWork capWord hCap state).1 =
      BinaryPRGWordControllerBooleanResourceSource.rowWords capacity state.reference.state := by
  subst capWord
  unfold rowWordsWithWork
  dsimp only
  rw [collectWithWork_reference state.packed state.packed_realizes]
  rw [BinaryPRGHeapAddressEnumeration.allWithWork_reference capacity]
  rfl

theorem rowWordsWithWork_bound (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowWordsWithWork capWord hCap state).2 ≤
      (BinaryPRGHeapAddressEnumeration.allWithWork capWord).2 +
      (BinaryPRGHeapAddressEnumeration.allWithWork capWord).1.length *
        (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
          2 * (capacity.width + 1) + 3) + 4 := by
  subst capWord
  have hRows := collectWithWork_bound state.packed
    (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).1
  change (collectWithWork state.packed
    (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).1).2 ≤
      (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).1.length *
        (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
          2 * (capacity.width + 1) + 3) + 1 at hRows
  unfold rowWordsWithWork
  dsimp only
  change (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).2 +
    (collectWithWork state.packed
      (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).1).2 + 3 ≤ _
  omega

theorem rowWordsWithWork_sourceBound (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowWordsWithWork capWord hCap state).2 ≤
      capWord.value * (20 * (capacity.width + 1) + 4) +
      12 * (capacity.width + 1) + 1 +
      capWord.value * (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
        2 * (capacity.width + 1) + 3) + 4 := by
  subst capWord
  have hLen : (BinaryPRGHeapAddressEnumeration.allWithWork capacity.cap).1.length =
      capacity.cap.value := by
    rw [BinaryPRGHeapAddressEnumeration.allWithWork_reference capacity]
    have h := congrArg List.length
      (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values capacity)
    simpa only [List.length_map,List.length_range] using h
  have hRows := rowWordsWithWork_bound capacity.cap rfl state
  rw [hLen] at hRows
  have hIds := BinaryPRGHeapAddressEnumeration.allWithWork_bound capacity.cap
  omega

theorem rowWordsWithWork_length (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowWordsWithWork capWord hCap state).1.length = n := by
  have h := congrArg List.length (rowWordsWithWork_reference capWord hCap state)
  rw [BinaryPRGWordControllerBooleanResourceSource.rowWords_reference
    capacity state.reference.state n hCount] at h
  simpa only [List.length_ofFn] using h

def rowTableWithWork (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    FixedArrayTable n SignedWord × ℕ :=
  let rows := rowWordsWithWork capWord hCap state
  (⟨rows.1.toArray,by
      rw [List.size_toArray,rowWordsWithWork_reference capWord hCap]
      rw [BinaryPRGWordControllerBooleanResourceSource.rowWords_reference capacity state.reference.state n hCount]
      exact List.length_ofFn⟩,
    rows.2 + rows.1.length + 2)

theorem rowTableWithWork_reference (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowTableWithWork capWord hCap state).1 =
      BinaryPRGWordControllerBooleanResourceSource.rowTable capacity state.reference.state n hCount := by
  unfold rowTableWithWork BinaryPRGWordControllerBooleanResourceSource.rowTable
  dsimp only
  simp only [rowWordsWithWork_reference capWord hCap]

theorem rowTableWithWork_bound (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (rowTableWithWork capWord hCap state).2 ≤
      capWord.value * (20 * (capacity.width + 1) + 4) +
      12 * (capacity.width + 1) + 1 +
      capWord.value * (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
        2 * (capacity.width + 1) + 3) + 4 + n + 2 := by
  have hWork := rowWordsWithWork_sourceBound capWord hCap state
  have hLength := rowWordsWithWork_length capWord hCap state
  unfold rowTableWithWork
  dsimp only
  omega

def materializedStateWithWork (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    BinaryResourceState.State n × ℕ :=
  let rows := rowTableWithWork capWord hCap state
  (⟨rows.1,state.active.map (fun address =>
      BinaryPRGWordControllerBooleanResourceSource.decodeIndex address n hCount)⟩,
    rows.2 + state.active.length * (capWord.bits.length + 1) + 2)

theorem materializedStateWithWork_reference (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (materializedStateWithWork capWord hCap state).1 =
      BinaryPRGWordControllerBooleanResourceSource.materializedState state.reference := by
  unfold materializedStateWithWork
    BinaryPRGWordControllerBooleanResourceSource.materializedState
  dsimp only
  rw [rowTableWithWork_reference capWord hCap,state.certified.choose_spec.2]
  rfl

def terminalWorkBound (capWord : FixedBinaryWord capacity.width)
    (state : Finished capacity n hCount) : ℕ :=
  capWord.value * (20 * (capacity.width + 1) + 4) +
    12 * (capacity.width + 1) + 1 +
    capWord.value * (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
      2 * (capacity.width + 1) + 3) + 4 + n + 2 +
    state.active.length * (capWord.bits.length + 1) + 5

def terminalUniformBound (capWord : FixedBinaryWord capacity.width)
    (state : Finished capacity n hCount) : ℕ :=
  capWord.value * (20 * (capacity.width + 1) + 4) +
    12 * (capacity.width + 1) + 1 +
    capWord.value * (BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
      2 * (capacity.width + 1) + 3) + 4 + n + 2 +
    n * (capacity.width + 1) + 5

theorem terminalWorkBound_le (capWord : FixedBinaryWord capacity.width)
    (state : Finished capacity n hCount) :
    terminalWorkBound capWord state ≤ terminalUniformBound capWord state := by
  have hActive := state.active_length_le
  have hMul := Nat.mul_le_mul_right (capWord.bits.length + 1) hActive
  rw [capWord.size] at hMul
  unfold terminalWorkBound terminalUniformBound
  rw [capWord.size]
  omega

theorem materializedStateWithWork_bound (capWord : FixedBinaryWord capacity.width)
    (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (materializedStateWithWork capWord hCap state).2 + 3 ≤
      terminalWorkBound capWord state := by
  have hRows := rowTableWithWork_bound capWord hCap state
  unfold materializedStateWithWork terminalWorkBound
  dsimp only
  omega

def materializeWithWork (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    BinaryResourcePair.Certified nativeCapacity × ℕ :=
  let drawn := materializedStateWithWork capWord hCap state
  (⟨drawn.1,
      (by
        have hs : drawn.1 =
            (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).state :=
          materializedStateWithWork_reference capWord hCap state
        rw [hs]
        exact (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).canonical),
      (by
        have hs : drawn.1 =
            (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).state :=
          materializedStateWithWork_reference capWord hCap state
        rw [hs]
        exact (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).nodup),
      (by
        have hs : drawn.1 =
            (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).state :=
          materializedStateWithWork_reference capWord hCap state
        rw [hs]
        exact (BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference).membership)⟩,
    drawn.2 + 3)

theorem materializeWithWork_reference (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (materializeWithWork nativeCapacity hTable capWord hCap state).1 =
      BinaryPRGWordControllerBooleanResourceSource.materializeTo nativeCapacity hTable state.reference := by
  apply BinaryPRGWordControllerBooleanResourceLoop.native_ext
  exact materializedStateWithWork_reference capWord hCap state

theorem materializeWithWork_bound (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (materializeWithWork nativeCapacity hTable capWord hCap state).2 ≤
      terminalWorkBound capWord state := by
  have h := materializedStateWithWork_bound capWord hCap state
  unfold materializeWithWork
  dsimp only
  exact h

theorem materializeWithWork_uniformBound (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (materializeWithWork nativeCapacity hTable capWord hCap state).2 ≤
      terminalUniformBound capWord state :=
  (materializeWithWork_bound nativeCapacity hTable capWord hCap state).trans
    (terminalWorkBound_le capWord state)

variable {m : ℕ}

theorem materializeSource_reference (nativeCapacity : FixedArrayTable m SignedWord)
    (capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore nativeCapacity).width)
    (hCap : capWord = (BinaryPRGHeapResourceSource.capStore nativeCapacity).cap)
    (state : Finished (BinaryPRGHeapResourceSource.capStore nativeCapacity) m
      (BinaryPRGHeapResourceSource.count nativeCapacity)) :
    (materializeWithWork nativeCapacity
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable nativeCapacity)
      capWord hCap state).1 =
      BinaryPRGWordControllerBooleanResourceSource.sourceMaterialize nativeCapacity state.reference := by
  apply BinaryPRGWordControllerBooleanResourceLoop.native_ext
  exact materializedStateWithWork_reference capWord hCap state

def runNativeWithWork (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable m SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerResource.Result seed nativeCapacity × ℕ :=
  let drawn := BinaryPRGHeapResourceSource.runWithRetainedCap seed nativeCapacity resource hC hR
  match drawn.1.2.1 with
  | none => ((none,drawn.1.2.2),drawn.2 + 2)
  | some state =>
      let terminal := materializeWithWork nativeCapacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable nativeCapacity)
        drawn.1.1
        (BinaryPRGHeapResourceSource.runWithRetainedCap_cap seed nativeCapacity resource hC hR)
        state
      ((some terminal.1,drawn.1.2.2),drawn.2 + terminal.2 + 4)

theorem runNativeWithWork_reference (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable m SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (runNativeWithWork seed nativeCapacity resource hC hR).1 =
      BinaryPRGWordControllerResource.initialRun seed nativeCapacity resource hC hR := by
  have hSource := BinaryPRGHeapResourceSource.runWithWork_original
    seed nativeCapacity resource hC hR
  rw [← BinaryPRGHeapResourceSource.runWithRetainedCap_result] at hSource
  unfold runNativeWithWork
  dsimp only
  cases hOutput : (BinaryPRGHeapResourceSource.runWithRetainedCap
    seed nativeCapacity resource hC hR).1.2.1 with
  | none =>
      simpa only [hOutput, BinaryPRGWordControllerBooleanResourceSource.result,
        BinaryPRGHeapResourceLoop.Result.reference,Option.map_none] using hSource
  | some state =>
      have hTerminal := materializeSource_reference nativeCapacity
        (BinaryPRGHeapResourceSource.runWithRetainedCap
          seed nativeCapacity resource hC hR).1.1
        (BinaryPRGHeapResourceSource.runWithRetainedCap_cap
          seed nativeCapacity resource hC hR) state
      simp only [hOutput, BinaryPRGWordControllerBooleanResourceSource.result,
        BinaryPRGHeapResourceLoop.Result.reference,Option.map_some] at hSource
      simpa only [hTerminal] using hSource

theorem runNativeWithWork_none_bound (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable m SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (hNone : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed nativeCapacity resource hC hR).1.2.1 = none) :
    (runNativeWithWork seed nativeCapacity resource hC hR).2 =
      (BinaryPRGHeapResourceSource.runWithRetainedCap
        seed nativeCapacity resource hC hR).2 + 2 := by
  unfold runNativeWithWork
  simp only [hNone]

theorem runNativeWithWork_some_bound (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable m SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (state : Finished (BinaryPRGHeapResourceSource.capStore nativeCapacity) m
      (BinaryPRGHeapResourceSource.count nativeCapacity))
    (hSome : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed nativeCapacity resource hC hR).1.2.1 = some state) :
    (runNativeWithWork seed nativeCapacity resource hC hR).2 ≤
      (BinaryPRGHeapResourceSource.runWithRetainedCap
        seed nativeCapacity resource hC hR).2 +
      terminalUniformBound
        (BinaryPRGHeapResourceSource.runWithRetainedCap
          seed nativeCapacity resource hC hR).1.1
        state + 4 := by
  have hTerminal := materializeWithWork_uniformBound nativeCapacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable nativeCapacity)
    (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed nativeCapacity resource hC hR).1.1
    (BinaryPRGHeapResourceSource.runWithRetainedCap_cap
      seed nativeCapacity resource hC hR) state
  unfold runNativeWithWork
  simp only [hSome]
  omega

end Blotto.BinaryPRGHeapResourceMaterialization
