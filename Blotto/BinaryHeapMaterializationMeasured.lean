import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryHeapEnumerationWidthMeasured
import Blotto.BinaryPRGHeapMaterializationLifetime

/-! Actual Boolean address enumeration, packed tape reads, row assembly and
active-index materialization return old data/trace and source work together.
There is no second materialization for its work field. Native array conversion,
index decoding, reference/observer/allocator realisation retain their existing
source-model boundary; this is not a complete native bit-machine theorem. -/
namespace Blotto.BinaryHeapMaterializationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def collect {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width) :
    List (Address width cap) → (List SignedWord × Trace) × ℕ
  | [] => (([],wrap 8 1 []),1)
  | address::rest =>
      let found := BinaryHeapPackedReadMeasured.read bids address.word
      let later := collect bids rest
      ((found.1.1::later.1.1,wrapList 1 16 2 [found.1.2,later.1.2]),
        found.2+later.2+2*(address.word.bits.length+1)+3)

theorem collect_erases {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width) (ids : List (Address width cap)) :
    (collect bids ids).1 = BinaryPRGHeapMaterializationLifetime.collectWithTrace bids ids := by
  induction ids with
  | nil => rfl
  | cons address rest ih => simp only [collect,BinaryPRGHeapMaterializationLifetime.collectWithTrace,
      BinaryHeapPackedReadMeasured.read_erases,ih]

theorem collect_work {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width) (ids : List (Address width cap)) :
    (collect bids ids).2 = (BinaryPRGHeapResourceMaterialization.collectWithWork bids ids).2 := by
  induction ids with
  | nil => rfl
  | cons address rest ih => simp only [collect,BinaryPRGHeapResourceMaterialization.collectWithWork,
      BinaryHeapPackedReadMeasured.read_work,ih]

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def rowWords (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (List SignedWord × Trace) × ℕ :=
  let ids := BinaryHeapEnumerationWidthMeasured.allFromBits capWord
  let addresses : List (Address capacity.width capacity.cap) := hCap ▸ ids.1.1
  let rows := collect state.packed addresses
  ((rows.1.1,wrap 16 2 [ids.1.2,rows.1.2]),ids.2+rows.2+3)

theorem rowWords_erases (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (rowWords capWord hCap state).1 = BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace capWord hCap state := by
  subst capWord
  simp only [rowWords,BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace,
    BinaryHeapEnumerationWidthMeasured.allFromBits_erases,collect_erases]

theorem rowWords_data (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (rowWords capWord hCap state).1.1 =
      (BinaryPRGHeapResourceMaterialization.rowWordsWithWork capWord hCap state).1 := by
  rw [rowWords_erases]
  exact BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace_erasure capWord hCap state

theorem rowWords_work (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (rowWords capWord hCap state).2 =
      (BinaryPRGHeapResourceMaterialization.rowWordsWithWork capWord hCap state).2 := by
  subst capWord
  simp only [rowWords,BinaryPRGHeapResourceMaterialization.rowWordsWithWork,
    BinaryHeapEnumerationWidthMeasured.allFromBits_work,BinaryHeapEnumerationWidthMeasured.allFromBits_erases,
    BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure,collect_work]

def rowTable (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (FixedArrayTable n SignedWord × Trace) × ℕ :=
  let rows := rowWords capWord hCap state
  have hLength : rows.1.1.length = n := by
    rw [rowWords_erases,BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace_length capWord hCap state]
  ((⟨rows.1.1.toArray,by rw [List.size_toArray,hLength]⟩,
    wrap (2*(n+1)^2+8) (n+4) [rows.1.2]),rows.2+rows.1.1.length+2)

theorem rowTable_erases (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    (rowTable capWord hCap state).1 = BinaryPRGHeapMaterializationLifetime.rowTableWithTrace capWord hCap state := by
  simp only [rowTable,BinaryPRGHeapMaterializationLifetime.rowTableWithTrace,rowWords_erases]

theorem rowTable_work (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) : (rowTable capWord hCap state).2 =
      (BinaryPRGHeapResourceMaterialization.rowTableWithWork capWord hCap state).2 := by
  simp only [rowTable,BinaryPRGHeapResourceMaterialization.rowTableWithWork,rowWords_work,rowWords_data]

def decode (address : Address capacity.width capacity.cap) : (Fin n × Trace) × ℕ :=
  (BinaryPRGHeapMaterializationLifetime.decodeWithTrace (hCount := hCount) address,address.word.bits.length+1)

def active : List (Address capacity.width capacity.cap) → (List (Fin n) × Trace) × ℕ
  | [] => (([],wrap 8 1 []),0)
  | address::rest =>
      let decoded := decode (hCount := hCount) address
      let later := active rest
      ((decoded.1.1::later.1.1,wrapList 1 8 2 [decoded.1.2,later.1.2]),decoded.2+later.2)

theorem active_erases (ids : List (Address capacity.width capacity.cap)) :
    (active (hCount := hCount) ids).1 = BinaryPRGHeapMaterializationLifetime.activeWithTrace (hCount := hCount) ids := by
  induction ids with
  | nil => rfl
  | cons address rest ih => simp only [active,decode,BinaryPRGHeapMaterializationLifetime.activeWithTrace,ih]

theorem active_work (ids : List (Address capacity.width capacity.cap)) :
    (active (hCount := hCount) ids).2 = ids.length*(capacity.width+1) := by
  induction ids with
  | nil => simp [active]
  | cons address rest ih =>
      simp only [active,decode,ih,List.length_cons,address.word.size,Nat.add_mul,one_mul]
      omega

def state (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) : (BinaryResourceState.State n × Trace) × ℕ :=
  let rows := rowTable capWord hCap finished
  let ids := active (hCount := hCount) finished.active
  ((⟨rows.1.1,ids.1.1⟩,wrap 16 2 [rows.1.2,ids.1.2]),rows.2+ids.2+2)

theorem state_erases (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) :
    (state capWord hCap finished).1 = BinaryPRGHeapMaterializationLifetime.stateWithTrace capWord hCap finished := by
  simp only [state,BinaryPRGHeapMaterializationLifetime.stateWithTrace,rowTable_erases,active_erases]

theorem state_data (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) : (state capWord hCap finished).1.1 =
      (BinaryPRGHeapResourceMaterialization.materializedStateWithWork capWord hCap finished).1 := by
  rw [state_erases]
  exact BinaryPRGHeapMaterializationLifetime.stateWithTrace_erasure capWord hCap finished

theorem state_work (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) : (state capWord hCap finished).2 =
      (BinaryPRGHeapResourceMaterialization.materializedStateWithWork capWord hCap finished).2 := by
  simp only [state,BinaryPRGHeapResourceMaterialization.materializedStateWithWork,rowTable_work,active_work,capWord.size]

def materialize (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    (BinaryResourcePair.Certified nativeCapacity × Trace) × ℕ :=
  let drawn := state capWord hCap finished
  ((⟨drawn.1.1,
    (by rw [state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.canonical),
    (by rw [state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.nodup),
    (by rw [state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.membership)⟩,
    wrap 16 2 [drawn.1.2]),drawn.2+3)

theorem materialize_erases (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    (materialize nativeCapacity hTable capWord hCap finished).1 =
      BinaryPRGHeapMaterializationLifetime.materializeWithTrace nativeCapacity hTable capWord hCap finished := by
  apply Prod.ext
  · apply BinaryPRGWordControllerBooleanResourceLoop.native_ext
    exact congrArg Prod.fst (state_erases capWord hCap finished)
  · simp only [materialize,BinaryPRGHeapMaterializationLifetime.materializeWithTrace,state_erases]

theorem materialize_work (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    (materialize nativeCapacity hTable capWord hCap finished).2 =
      (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).2 := by
  simp only [materialize,BinaryPRGHeapResourceMaterialization.materializeWithWork,state_work]

end Blotto.BinaryHeapMaterializationMeasured
