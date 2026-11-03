import Blotto.BinaryPackedReadPlan
import Blotto.BinaryHeapMaterializationPlan
import Blotto.BinaryHeapEnumerationPlan
import Blotto.BinaryHeapMaterializationMeasured

/-! Final physical materialization consumes the actual planned packed reader
at the reached absolute depth. Every preceding materializer plan and source
charge is exact; reached reader emissions are returned separately. -/
namespace Blotto.BinaryPackedMaterializationPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceDepth
open BinaryHeapEnumerationPlan (view offset)
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def readAtWithEmission {width : ℕ} (bids : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :=
  BinaryNumericalReadbackPlan.finish (BinaryPackedReadPlan.readAt bids address depth)

theorem readAt_compat {width : ℕ} (bids : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :
    (readAtWithEmission bids address depth).1 = BinaryHeapPackedReadMeasured.readAt bids address depth := by
  rw [readAtWithEmission,BinaryNumericalReadbackPlan.finish_record,BinaryPackedReadPlan.read_refines]

theorem readAt_price {width : ℕ} (bids : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :
    (readAtWithEmission bids address depth).2 ≤ 25*(readAtWithEmission bids address depth).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (BinaryPackedReadPlan.read_bound bids address depth)

def collectAt {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width) :
    List (Address width cap) → ℕ → ((List SignedWord × Plan) × ℕ) × ℕ
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),1),0)
  | address::rest,depth =>
      let produced := readAtWithEmission bids address.word (depth+2)
      let returned := collectAt bids rest (depth+2)
      let found := produced.1
      let later := returned.1
      (((found.1.1::later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
        (.join (.block found.1.2) later.1.2)),found.2+later.2+2*(address.word.bits.length+1)+3),produced.2+returned.2)

theorem collectAt_compat {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width)
    (ids : List (Address width cap)) (depth : ℕ) :
    (collectAt bids ids depth).1 = BinaryHeapMaterializationPlan.collectAt bids ids depth := by
  induction ids generalizing depth with
  | nil => rfl
  | cons address rest ih =>
      simp only [collectAt,BinaryHeapMaterializationPlan.collectAt,readAt_compat,ih]

theorem collectAt_price {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width)
    (ids : List (Address width cap)) (depth : ℕ) :
    (collectAt bids ids depth).2 ≤ 25*BinaryTracePlanMeasured.payload (collectAt bids ids depth).1.1.2 := by
  induction ids generalizing depth with
  | nil => simp only [collectAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega
  | cons address rest ih =>
      have hr := readAt_price bids address.word (depth+2)
      have hl := ih (depth+2)
      simp only [collectAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
      omega


variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def rowWordsAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : ((List SignedWord × Plan) × ℕ) × ℕ :=
  let ids := BinaryHeapEnumerationPlan.allFromBitsAt capWord (depth+2)
  let addresses : List (Address capacity.width capacity.cap) := hCap ▸ ids.1.1
  let produced := collectAt finished.packed addresses (depth+2)
  let rows := produced.1
  (((rows.1.1,.join (.block [.frames (depth+2),.arrayAllocation 16]) (.join ids.1.2 rows.1.2)),ids.2+rows.2+3),produced.2)

theorem rowWordsAt_compat (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (rowWordsAt capWord hCap finished depth).1 = BinaryHeapMaterializationPlan.rowWordsAt capWord hCap finished depth := by
  simp only [rowWordsAt,BinaryHeapMaterializationPlan.rowWordsAt,collectAt_compat]

theorem rowWordsAt_price (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (rowWordsAt capWord hCap finished depth).2 ≤ 25*BinaryTracePlanMeasured.payload (rowWordsAt capWord hCap finished depth).1.1.2 := by
  have h := collectAt_price finished.packed (hCap ▸ (BinaryHeapEnumerationPlan.allFromBitsAt capWord (depth+2)).1.1) (depth+2)
  simp only [rowWordsAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def rowTableAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : ((FixedArrayTable n SignedWord × Plan) × ℕ) × ℕ :=
  let produced := rowWordsAt capWord hCap finished (depth+2)
  let rows := produced.1
  have hRows : rows.1.1 = (BinaryHeapMaterializationMeasured.rowWords capWord hCap finished).1.1 :=
    (congrArg (fun out => out.1.1) (rowWordsAt_compat capWord hCap finished (depth+2))).trans
      (congrArg (fun out => out.1.1) (BinaryHeapMaterializationPlan.rowWordsAt_refines capWord hCap finished (depth+2)))
  have hLength : rows.1.1.length = n := by
    rw [hRows,BinaryHeapMaterializationMeasured.rowWords_erases,
      BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace_length capWord hCap finished]
  (((⟨rows.1.1.toArray,by rw [List.size_toArray,hLength]⟩,
    .join (.block [.frames (depth+n+4),.arrayAllocation (2*(n+1)^2+8)]) rows.1.2),rows.2+rows.1.1.length+2),produced.2)

theorem rowTableAt_compat (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (rowTableAt capWord hCap finished depth).1 = BinaryHeapMaterializationPlan.rowTableAt capWord hCap finished depth := by
  simp only [rowTableAt,BinaryHeapMaterializationPlan.rowTableAt,rowWordsAt_compat]

theorem rowTableAt_price (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (rowTableAt capWord hCap finished depth).2 ≤ 25*BinaryTracePlanMeasured.payload (rowTableAt capWord hCap finished depth).1.1.2 := by
  have h := rowWordsAt_price capWord hCap finished (depth+2)
  simp only [rowTableAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def stateAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : ((BinaryResourceState.State n × Plan) × ℕ) × ℕ :=
  let produced := rowTableAt capWord hCap finished (depth+2)
  let rows := produced.1
  let ids := BinaryHeapMaterializationPlan.activeAt (hCount := hCount) finished.active (depth+2)
  (((⟨rows.1.1,ids.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16]) (.join rows.1.2 ids.1.2)),rows.2+ids.2+2),produced.2)

theorem stateAt_compat (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (stateAt capWord hCap finished depth).1 = BinaryHeapMaterializationPlan.stateAt capWord hCap finished depth := by
  simp only [stateAt,BinaryHeapMaterializationPlan.stateAt,rowTableAt_compat]

theorem stateAt_price (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    (stateAt capWord hCap finished depth).2 ≤ 25*BinaryTracePlanMeasured.payload (stateAt capWord hCap finished depth).1.1.2 := by
  have h := rowTableAt_price capWord hCap finished (depth+2)
  simp only [stateAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def materializeAt (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) : ((BinaryResourcePair.Certified nativeCapacity × Plan) × ℕ) × ℕ :=
  let produced := stateAt capWord hCap finished (depth+2)
  let drawn := produced.1
  have hd : drawn.1.1 = (BinaryHeapMaterializationMeasured.state capWord hCap finished).1.1 :=
    (congrArg (fun out => out.1.1) (stateAt_compat capWord hCap finished (depth+2))).trans
      (congrArg (fun out => out.1.1) (BinaryHeapMaterializationPlan.stateAt_refines capWord hCap finished (depth+2)))
  (((⟨drawn.1.1,
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.canonical),
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.nodup),
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.membership)⟩,
    .join (.block [.frames (depth+2),.arrayAllocation 16]) drawn.1.2),drawn.2+3),produced.2)

theorem materializeAt_compat (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) :
    (materializeAt nativeCapacity hTable capWord hCap finished depth).1 = BinaryHeapMaterializationPlan.materializeAt nativeCapacity hTable capWord hCap finished depth := by
  simp only [materializeAt,BinaryHeapMaterializationPlan.materializeAt,stateAt_compat]

theorem materializeAt_price (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) :
    (materializeAt nativeCapacity hTable capWord hCap finished depth).2 ≤ 25*BinaryTracePlanMeasured.payload (materializeAt nativeCapacity hTable capWord hCap finished depth).1.1.2 := by
  have h := stateAt_price capWord hCap finished (depth+2)
  simp only [materializeAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

end Blotto.BinaryPackedMaterializationPlan
