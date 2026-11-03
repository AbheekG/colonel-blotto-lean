import Blotto.BinaryHeapEnumerationPlan
import Blotto.BinaryHeapMaterializationMeasured

/-! The selected materializer builds one absolute-depth trace plan, including
Boolean enumeration, packed reads, row assembly and active-index decoding.
Its reference erasure preserves the complete preceding value/trace/work record.
Native array/scalar/reference/allocator prices remain separate. -/
namespace Blotto.BinaryHeapMaterializationPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceDepth
open BinaryHeapEnumerationPlan (view offset)
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem packed_read_at {width : ℕ} (bids : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :
    BinaryHeapPackedReadMeasured.readAt bids address depth =
      offset depth (BinaryHeapPackedReadMeasured.read bids address) := by
  apply Prod.ext
  · simp only [offset,BinaryHeapPackedReadMeasured.readAt_erases,BinaryHeapPackedReadMeasured.read_erases]
  · simp only [offset,BinaryHeapPackedReadMeasured.readAt_work,BinaryHeapPackedReadMeasured.read_work]

def collectAt {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width) :
    List (Address width cap) → ℕ → (List SignedWord × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | address::rest,depth =>
      let found := BinaryHeapPackedReadMeasured.readAt bids address.word (depth+2)
      let later := collectAt bids rest (depth+2)
      ((found.1.1::later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
        (.join (.block found.1.2) later.1.2)),found.2+later.2+2*(address.word.bits.length+1)+3)

theorem collectAt_refines {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width)
    (ids : List (Address width cap)) (depth : ℕ) :
    view (collectAt bids ids depth) = offset depth (BinaryHeapMaterializationMeasured.collect bids ids) := by
  induction ids generalizing depth with
  | nil => rfl
  | cons address rest ih =>
      have h := ih (depth+2)
      simp only [view,offset] at h
      have hv := congrArg (fun out => out.1.1) h

      dsimp only at hv
      have ht := congrArg (fun out => out.1.2) h
      dsimp only at ht
      have hw := congrArg (fun out => out.2) h
      dsimp only at hw
      simp only [view,offset,collectAt,BinaryHeapMaterializationMeasured.collect,packed_read_at,denote,
        hv,ht,hw,BinaryPRGHeapTraceUsage.wrapList,BinaryPRGHeapTraceUsage.wrap,
        BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil,List.append_assoc]
      rfl

theorem collectAt_budget {width : ℕ} {cap : FixedBinaryWord width} (bids : Packed width)
    (ids : List (Address width cap)) (depth : ℕ) :
    payload (collectAt bids ids depth).1.2+nodes (collectAt bids ids depth).1.2 ≤
      8*((collectAt bids ids depth).2+1) := by
  induction ids generalizing depth with
  | nil => simp [collectAt,payload,nodes]
  | cons address rest ih =>
      have h := ih (depth+2)
      have hr := BinaryHeapPackedReadMeasured.readAt_trace_work bids address.word (depth+2)
      simp only [collectAt,payload,nodes,List.length_cons,List.length_nil]
      omega

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def rowWordsAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : (List SignedWord × Plan) × ℕ :=
  let ids := BinaryHeapEnumerationPlan.allFromBitsAt capWord (depth+2)
  let addresses : List (Address capacity.width capacity.cap) := hCap ▸ ids.1.1
  let rows := collectAt finished.packed addresses (depth+2)
  ((rows.1.1,.join (.block [.frames (depth+2),.arrayAllocation 16]) (.join ids.1.2 rows.1.2)),ids.2+rows.2+3)

theorem rowWordsAt_refines (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    view (rowWordsAt capWord hCap finished depth) =
      offset depth (BinaryHeapMaterializationMeasured.rowWords capWord hCap finished) := by
  subst capWord
  have hi := BinaryHeapEnumerationPlan.allFromBitsAt_refines capacity.cap (depth+2)
  simp only [view,offset] at hi
  have hv := congrArg (fun out => out.1.1) hi

  dsimp only at hv
  have ht := congrArg (fun out => out.1.2) hi
  dsimp only at ht
  have hw := congrArg (fun out => out.2) hi
  dsimp only at hw
  have hc := collectAt_refines finished.packed (BinaryHeapEnumerationWidthMeasured.allFromBits capacity.cap).1.1 (depth+2)
  simp only [view,offset] at hc
  have hcv := congrArg (fun out => out.1.1) hc

  dsimp only at hcv
  have hct := congrArg (fun out => out.1.2) hc
  dsimp only at hct
  have hcw := congrArg (fun out => out.2) hc
  dsimp only at hcw
  simp only [view,offset,rowWordsAt,BinaryHeapMaterializationMeasured.rowWords,denote,hv,ht,hw,hcv,hct,hcw,
    BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil]
  rfl

theorem rowWordsAt_budget (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    payload (rowWordsAt capWord hCap finished depth).1.2+nodes (rowWordsAt capWord hCap finished depth).1.2 ≤
      16*((rowWordsAt capWord hCap finished depth).2+1) := by
  have hi := BinaryHeapEnumerationPlan.allFromBitsAt_budget capWord (depth+2)
  have hc := collectAt_budget finished.packed (hCap ▸ (BinaryHeapEnumerationPlan.allFromBitsAt capWord (depth+2)).1.1) (depth+2)
  simp only [rowWordsAt,payload,nodes,List.length_cons,List.length_nil]
  omega

def rowTableAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : (FixedArrayTable n SignedWord × Plan) × ℕ :=
  let rows := rowWordsAt capWord hCap finished (depth+2)
  have hRows : rows.1.1 = (BinaryHeapMaterializationMeasured.rowWords capWord hCap finished).1.1 :=
    congrArg (fun out => out.1.1) (rowWordsAt_refines capWord hCap finished (depth+2))
  have hLength : rows.1.1.length = n := by
    rw [hRows,BinaryHeapMaterializationMeasured.rowWords_erases,
      BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace_length capWord hCap finished]
  ((⟨rows.1.1.toArray,by rw [List.size_toArray,hLength]⟩,
    .join (.block [.frames (depth+n+4),.arrayAllocation (2*(n+1)^2+8)]) rows.1.2),rows.2+rows.1.1.length+2)

theorem rowTableAt_refines (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    view (rowTableAt capWord hCap finished depth) =
      offset depth (BinaryHeapMaterializationMeasured.rowTable capWord hCap finished) := by
  have h := rowWordsAt_refines capWord hCap finished (depth+2)
  simp only [view,offset] at h
  have hv := congrArg (fun out => out.1.1) h

  dsimp only at hv
  have ht := congrArg (fun out => out.1.2) h
  dsimp only at ht
  have hw := congrArg (fun out => out.2) h
  dsimp only at hw
  simp only [view,offset,rowTableAt,BinaryHeapMaterializationMeasured.rowTable,denote,hv,ht,hw,
    BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil]
  rfl

theorem rowTableAt_budget (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    payload (rowTableAt capWord hCap finished depth).1.2+nodes (rowTableAt capWord hCap finished depth).1.2 ≤
      16*((rowTableAt capWord hCap finished depth).2+1) := by
  have h := rowWordsAt_budget capWord hCap finished (depth+2)
  simp only [rowTableAt,payload,nodes,List.length_cons,List.length_nil]
  omega

def decodeAt (address : Address capacity.width capacity.cap) (depth : ℕ) : (Fin n × Plan) × ℕ :=
  ((BinaryPRGWordControllerBooleanResourceSource.decodeIndex address n hCount,
    .block [.frames (depth+address.word.bits.length+2),.arrayAllocation 16]),address.word.bits.length+1)

theorem decodeAt_refines (address : Address capacity.width capacity.cap) (depth : ℕ) :
    view (decodeAt (hCount := hCount) address depth) =
      offset depth (BinaryHeapMaterializationMeasured.decode (hCount := hCount) address) := by
  simp only [view,offset,decodeAt,BinaryHeapMaterializationMeasured.decode,
    BinaryPRGHeapMaterializationLifetime.decodeWithTrace,denote,BinaryPRGHeapTraceUsage.wrap,
    BinaryPRGHeapTraceUsage.combine,List.append_nil]
  rfl

def activeAt : List (Address capacity.width capacity.cap) → ℕ → (List (Fin n) × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),0)
  | address::rest,depth =>
      let decoded := decodeAt (hCount := hCount) address (depth+2)
      let later := activeAt rest (depth+2)
      ((decoded.1.1::later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 8])
        (.join decoded.1.2 later.1.2)),decoded.2+later.2)

theorem activeAt_refines (ids : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    view (activeAt (hCount := hCount) ids depth) =
      offset depth (BinaryHeapMaterializationMeasured.active (hCount := hCount) ids) := by
  induction ids generalizing depth with
  | nil => rfl
  | cons address rest ih =>
      have h := ih (depth+2)
      simp only [view,offset] at h
      have hv := congrArg (fun out => out.1.1) h

      dsimp only at hv
      have ht := congrArg (fun out => out.1.2) h
      dsimp only at ht
      have hw := congrArg (fun out => out.2) h
      dsimp only at hw
      simp only [view,offset,activeAt,decodeAt,BinaryHeapMaterializationMeasured.active,
        BinaryHeapMaterializationMeasured.decode,BinaryPRGHeapMaterializationLifetime.decodeWithTrace,denote,hv,ht,hw,
        BinaryPRGHeapTraceUsage.wrapList,BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,
        under_append,under_compose,List.append_nil,List.append_assoc]
      rfl

theorem activeAt_budget (ids : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    payload (activeAt (hCount := hCount) ids depth).1.2+nodes (activeAt (hCount := hCount) ids depth).1.2 ≤
      16*((activeAt (hCount := hCount) ids depth).2+1) := by
  induction ids generalizing depth with
  | nil => simp [activeAt,payload,nodes]
  | cons address rest ih =>
      have h := ih (depth+2)
      simp only [activeAt,decodeAt,payload,nodes,List.length_cons,List.length_nil]
      omega

def stateAt (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) : (BinaryResourceState.State n × Plan) × ℕ :=
  let rows := rowTableAt capWord hCap finished (depth+2)
  let ids := activeAt (hCount := hCount) finished.active (depth+2)
  ((⟨rows.1.1,ids.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16]) (.join rows.1.2 ids.1.2)),rows.2+ids.2+2)

theorem stateAt_refines (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    view (stateAt capWord hCap finished depth) =
      offset depth (BinaryHeapMaterializationMeasured.state capWord hCap finished) := by
  have hr := rowTableAt_refines capWord hCap finished (depth+2)
  have hi := activeAt_refines (hCount := hCount) finished.active (depth+2)
  simp only [view,offset] at hr hi
  have hv := congrArg (fun out => out.1.1) hr

  dsimp only at hv
  have ht := congrArg (fun out => out.1.2) hr
  dsimp only at ht
  have hw := congrArg (fun out => out.2) hr
  dsimp only at hw
  have hiv := congrArg (fun out => out.1.1) hi
  dsimp only at hiv
  have hit := congrArg (fun out => out.1.2) hi
  dsimp only at hit
  have hiw := congrArg (fun out => out.2) hi
  dsimp only at hiw
  simp only [view,offset,stateAt,BinaryHeapMaterializationMeasured.state,denote,hv,ht,hw,hiv,hit,hiw,
    BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil]
  rfl

theorem stateAt_budget (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (finished : Finished capacity n hCount) (depth : ℕ) :
    payload (stateAt capWord hCap finished depth).1.2+nodes (stateAt capWord hCap finished depth).1.2 ≤
      16*((stateAt capWord hCap finished depth).2+1) := by
  have hr := rowTableAt_budget capWord hCap finished (depth+2)
  have hi := activeAt_budget (hCount := hCount) finished.active (depth+2)
  simp only [stateAt,payload,nodes,List.length_cons,List.length_nil]
  omega

def materializeAt (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) : (BinaryResourcePair.Certified nativeCapacity × Plan) × ℕ :=
  let drawn := stateAt capWord hCap finished (depth+2)
  have hd : drawn.1.1 = (BinaryHeapMaterializationMeasured.state capWord hCap finished).1.1 :=
    congrArg (fun out => out.1.1) (stateAt_refines capWord hCap finished (depth+2))
  ((⟨drawn.1.1,
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.canonical),
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.nodup),
    (by rw [hd,BinaryHeapMaterializationMeasured.state_data]; exact (BinaryPRGHeapResourceMaterialization.materializeWithWork nativeCapacity hTable capWord hCap finished).1.membership)⟩,
    .join (.block [.frames (depth+2),.arrayAllocation 16]) drawn.1.2),drawn.2+3)

theorem materializeAt_refines (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) : view (materializeAt nativeCapacity hTable capWord hCap finished depth) =
      offset depth (BinaryHeapMaterializationMeasured.materialize nativeCapacity hTable capWord hCap finished) := by
  have h := stateAt_refines capWord hCap finished (depth+2)
  simp only [view,offset] at h
  have hv := congrArg (fun out => out.1.1) h

  dsimp only at hv
  have ht := congrArg (fun out => out.1.2) h
  dsimp only at ht
  have hw := congrArg (fun out => out.2) h
  dsimp only at hw
  apply Prod.ext
  · apply Prod.ext
    · apply BinaryPRGWordControllerBooleanResourceLoop.native_ext
      exact hv
    · simp only [view,offset,materializeAt,BinaryHeapMaterializationMeasured.materialize,denote,ht,
        BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil]
      rfl
  · simp only [view,offset,materializeAt,BinaryHeapMaterializationMeasured.materialize,hw]

theorem materializeAt_budget (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) :
    payload (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2+
      nodes (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2 ≤
      16*((materializeAt nativeCapacity hTable capWord hCap finished depth).2+1) := by
  have h := stateAt_budget capWord hCap finished (depth+2)
  simp only [materializeAt,payload,nodes,List.length_cons,List.length_nil]
  omega

def execute (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    ((BinaryResourcePair.Certified nativeCapacity × Trace) × ℕ) × ℕ :=
  let planned := materializeAt nativeCapacity hTable capWord hCap finished 0
  let emitted := emitFull planned.1.2 []
  (((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2)

theorem execute_compat (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    (execute nativeCapacity hTable capWord hCap finished).1 =
      BinaryHeapMaterializationMeasured.materialize nativeCapacity hTable capWord hCap finished := by
  have h := materializeAt_refines nativeCapacity hTable capWord hCap finished 0
  simpa only [execute,emitFull_erases,emit_data,List.append_nil,view,offset,under_zero] using h

theorem execute_emission (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    (execute nativeCapacity hTable capWord hCap finished).2 ≤
      80*((execute nativeCapacity hTable capWord hCap finished).1.2+1) := by
  have h := emitFull_total (materializeAt nativeCapacity hTable capWord hCap finished 0).1.2 []
    (16*((materializeAt nativeCapacity hTable capWord hCap finished 0).2+1))
    (materializeAt_budget nativeCapacity hTable capWord hCap finished 0)
  dsimp only [execute]
  omega

theorem materialize_plan_references (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) :
    planReferences (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2 ≤
      32*((materializeAt nativeCapacity hTable capWord hCap finished depth).2+1) := by
  have h := planReferences_bound (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2
  have hb := materializeAt_budget nativeCapacity hTable capWord hCap finished depth
  omega

theorem materialize_emit_frames (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount)
    (depth : ℕ) :
    emitFrames (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2 ≤
      16*((materializeAt nativeCapacity hTable capWord hCap finished depth).2+1)+1 := by
  have h := emitFrames_bound (materializeAt nativeCapacity hTable capWord hCap finished depth).1.2
  have hb := materializeAt_budget nativeCapacity hTable capWord hCap finished depth
  omega

theorem execute_emission_width (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (finished : Finished capacity n hCount) :
    binaryWordWidth (execute nativeCapacity hTable capWord hCap finished).2 ≤
      binaryWordWidth (80*((execute nativeCapacity hTable capWord hCap finished).1.2+1)) :=
  binaryWordWidth_mono (execute_emission nativeCapacity hTable capWord hCap finished)

end Blotto.BinaryHeapMaterializationPlan
