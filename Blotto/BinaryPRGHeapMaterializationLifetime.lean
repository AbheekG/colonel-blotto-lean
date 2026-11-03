import Blotto.BinaryPRGHeapEnumerationLifetime
import Blotto.BinaryPRGHeapResourceMaterialization

/-! Native resource materialization consumes traced physical tape reads and
Boolean address enumeration. Row-list/array and decoded-index records remain
retained; scalar bit layouts and host allocator interpretation are separate. -/

namespace Blotto.BinaryPRGHeapMaterializationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1500000

variable {width : ℕ} {cap : FixedBinaryWord width}

def collectWithTrace (bids : Packed width) : List (Address width cap) → List SignedWord × Trace
  | [] => ([],wrap 8 1 [])
  | address :: rest =>
      let found := BinaryPRGHeapPackedLifetime.readWithTrace bids address.word
      let later := collectWithTrace bids rest
      (found.1 :: later.1,wrapList 1 16 2 [found.2,later.2])

theorem collectWithTrace_erasure (bids : Packed width) (ids : List (Address width cap)) :
    (collectWithTrace bids ids).1 = (BinaryPRGHeapResourceMaterialization.collectWithWork bids ids).1 := by
  induction ids with
  | nil => rfl
  | cons address rest ih => simp only [collectWithTrace,BinaryPRGHeapResourceMaterialization.collectWithWork,
      BinaryPRGHeapPackedLifetime.readWithTrace_erasure,ih]

def collectEnvelope (count H depth : ℕ) : ℕ := count * (readEnvelope H depth + 24) + 9

theorem collectWithTrace_usage (bids : Packed width) (ids : List (Address width cap)) (H : ℕ)
    (hH : bids.heap.tape.length ≤ H) :
    usage (collectWithTrace bids ids).2 ≤ collectEnvelope ids.length H width := by
  induction ids with
  | nil => simp [collectWithTrace,collectEnvelope,usage,BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have hRead := read_usage bids address.word H hH
      have hw := wrapList_usage 1 16 2 [(BinaryPRGHeapPackedLifetime.readWithTrace bids address.word).2,
        (collectWithTrace bids rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      unfold collectWithTrace collectEnvelope
      unfold collectEnvelope at ih
      simp only [List.length_cons]
      nlinarith

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def rowWordsWithTrace (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : List SignedWord × Trace :=
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (Address capacity.width capacity.cap) := hCap ▸ ids.1
  let rows := collectWithTrace state.packed addresses
  (rows.1,wrap 16 2 [ids.2,rows.2])

theorem rowWordsWithTrace_erasure (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (rowWordsWithTrace capWord hCap state).1 =
      (BinaryPRGHeapResourceMaterialization.rowWordsWithWork capWord hCap state).1 := by
  subst capWord
  simp only [rowWordsWithTrace,BinaryPRGHeapResourceMaterialization.rowWordsWithWork,
    BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,collectWithTrace_erasure]

theorem rowWordsWithTrace_length (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (rowWordsWithTrace capWord hCap state).1.length = n := by
  rw [rowWordsWithTrace_erasure]
  exact BinaryPRGHeapResourceMaterialization.rowWordsWithWork_length capWord hCap state

def rowTableWithTrace (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : FixedArrayTable n SignedWord × Trace :=
  let rows := rowWordsWithTrace capWord hCap state
  (⟨rows.1.toArray,by rw [List.size_toArray,rowWordsWithTrace_length capWord hCap state]⟩,
    wrap (2 * (n + 1)^2 + 8) (n + 4) [rows.2])

theorem rowTableWithTrace_erasure (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (rowTableWithTrace capWord hCap state).1 =
      (BinaryPRGHeapResourceMaterialization.rowTableWithWork capWord hCap state).1 := by
  simp only [rowTableWithTrace,BinaryPRGHeapResourceMaterialization.rowTableWithWork,rowWordsWithTrace_erasure]

def decodeWithTrace (address : Address capacity.width capacity.cap) : Fin n × Trace :=
  (BinaryPRGWordControllerBooleanResourceSource.decodeIndex address n hCount,
    wrap 16 (address.word.bits.length + 2) [])

def activeWithTrace : List (Address capacity.width capacity.cap) → List (Fin n) × Trace
  | [] => ([],wrap 8 1 [])
  | address :: rest =>
      let decoded := decodeWithTrace (hCount := hCount) address
      let later := activeWithTrace rest
      (decoded.1 :: later.1,wrapList 1 8 2 [decoded.2,later.2])

theorem activeWithTrace_erasure (ids : List (Address capacity.width capacity.cap)) :
    (activeWithTrace (hCount := hCount) ids).1 =
      ids.map (fun address => BinaryPRGWordControllerBooleanResourceSource.decodeIndex address n hCount) := by
  induction ids with
  | nil => rfl
  | cons address rest ih => simp only [activeWithTrace,decodeWithTrace,List.map_cons,ih]

theorem activeWithTrace_usage (ids : List (Address capacity.width capacity.cap)) :
    usage (activeWithTrace (hCount := hCount) ids).2 ≤ ids.length * (capacity.width + 40) + 9 := by
  induction ids with
  | nil => simp [activeWithTrace,usage,BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have hd := wrap_usage 16 (address.word.bits.length + 2) []
      have hw := wrapList_usage 1 8 2 [(decodeWithTrace (hCount := hCount) address).2,
        (activeWithTrace (hCount := hCount) rest).2]
      simp only [List.map_nil,List.map_cons,List.sum_nil,List.sum_cons] at hd hw
      unfold activeWithTrace
      change usage (wrapList 1 8 2 [(decodeWithTrace (hCount := hCount) address).2,
        (activeWithTrace (hCount := hCount) rest).2]) ≤ _
      change usage (decodeWithTrace (hCount := hCount) address).2 ≤ _ at hd
      rw [address.word.size] at hd
      simp only [List.length_cons]
      nlinarith

def stateWithTrace (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : BinaryResourceState.State n × Trace :=
  let rows := rowTableWithTrace capWord hCap state
  let ids := activeWithTrace (hCount := hCount) state.active
  (⟨rows.1,ids.1⟩,wrap 16 2 [rows.2,ids.2])

theorem stateWithTrace_erasure (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (stateWithTrace capWord hCap state).1 =
      (BinaryPRGHeapResourceMaterialization.materializedStateWithWork capWord hCap state).1 := by
  simp only [stateWithTrace,BinaryPRGHeapResourceMaterialization.materializedStateWithWork,
    rowTableWithTrace_erasure,activeWithTrace_erasure]

def materializeWithTrace (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    BinaryResourcePair.Certified nativeCapacity × Trace :=
  let drawn := stateWithTrace capWord hCap state
  (⟨drawn.1,
    (by rw [stateWithTrace_erasure]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap state).1.canonical),
    (by rw [stateWithTrace_erasure]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap state).1.nodup),
    (by rw [stateWithTrace_erasure]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap state).1.membership)⟩,
    wrap 16 2 [drawn.2])

theorem materializeWithTrace_erasure (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    (materializeWithTrace nativeCapacity hTable capWord hCap state).1 =
      (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap state).1 := by
  apply BinaryPRGWordControllerBooleanResourceLoop.native_ext
  exact stateWithTrace_erasure capWord hCap state

def rowEnvelope (n H depth : ℕ) : ℕ :=
  BinaryPRGHeapEnumerationLifetime.envelope n depth + collectEnvelope n H depth + 22

theorem rowWordsWithTrace_usage (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) (H : ℕ) (hH : state.heap.tape.length ≤ H) :
    usage (rowWordsWithTrace capWord hCap state).2 ≤ rowEnvelope n H capacity.width := by
  subst capWord
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capacity.cap
  have hLength : ids.1.length = n := by
    dsimp only [ids]
    rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,BinaryPRGHeapAddressEnumeration.allWithWork_reference]
    have h := congrArg List.length (BinaryPRGWordControllerBooleanResourceInitial.allAddresses_values capacity)
    simpa only [List.length_map,List.length_range,← hCount] using h
  have hCollect := collectWithTrace_usage state.packed ids.1 H hH
  rw [hLength] at hCollect
  have hIds := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_usage capacity.cap
  have hCapValue : capacity.cap.value = n := hCount.symm
  have hEnum : usage ids.2 ≤ BinaryPRGHeapEnumerationLifetime.envelope n capacity.width :=
    hIds.trans_eq (congrArg (fun count => BinaryPRGHeapEnumerationLifetime.envelope count capacity.width) hCapValue)
  have hw := wrap_usage 16 2 [ids.2,(collectWithTrace state.packed ids.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold rowWordsWithTrace rowEnvelope
  change usage (wrap 16 2 [ids.2,(collectWithTrace state.packed ids.1).2]) ≤ _
  omega

theorem rowTableWithTrace_usage (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) (H : ℕ) (hH : state.heap.tape.length ≤ H) :
    usage (rowTableWithTrace capWord hCap state).2 ≤ rowEnvelope n H capacity.width + 2 * (n + 1)^2 + n + 14 := by
  have h := rowWordsWithTrace_usage capWord hCap state H hH
  have hw := wrap_usage (2 * (n + 1)^2 + 8) (n + 4) [(rowWordsWithTrace capWord hCap state).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold rowTableWithTrace
  dsimp only
  omega

def envelope (n H depth : ℕ) : ℕ := rowEnvelope n H depth + 2 * (n + 1)^2 + n + n * (depth + 40) + 100

theorem materializeWithTrace_usage (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (state : Finished capacity n hCount)
    (H : ℕ) (hH : state.heap.tape.length ≤ H) :
    usage (materializeWithTrace nativeCapacity hTable capWord hCap state).2 ≤ envelope n H capacity.width := by
  have hRows := rowTableWithTrace_usage capWord hCap state H hH
  have hIds := activeWithTrace_usage (hCount := hCount) state.active
  have hm := Nat.mul_le_mul_right (capacity.width + 40) state.active_length_le
  have hState := wrap_usage 16 2 [(rowTableWithTrace capWord hCap state).2,(activeWithTrace (hCount := hCount) state.active).2]
  have hw := wrap_usage 16 2 [(stateWithTrace capWord hCap state).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hState hw
  change usage (stateWithTrace capWord hCap state).2 ≤ _ at hState
  unfold materializeWithTrace
  dsimp only
  unfold envelope
  omega

theorem materialize_all_prefix (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (state : Finished capacity n hCount)
    (H : ℕ) (hH : state.heap.tape.length ≤ H) (borrowed steps : ℕ) :
    retainedHeap borrowed (materializeWithTrace nativeCapacity hTable capWord hCap state).2 steps ≤ borrowed + envelope n H capacity.width ∧
      framePeak ((materializeWithTrace nativeCapacity hTable capWord hCap state).2.take steps) ≤ envelope n H capacity.width :=
  all_prefix _ _ (materializeWithTrace_usage nativeCapacity hTable capWord hCap state H hH) borrowed steps

end Blotto.BinaryPRGHeapMaterializationLifetime
