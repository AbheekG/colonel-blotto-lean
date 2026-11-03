import Blotto.BinaryHeapReadPlan
import Blotto.BinaryHeapAllocatorPlan
import Blotto.BinaryHeapWriteMeasured
import Blotto.BinaryPRGHeapWriteLifetime
import Blotto.BinarySeedCursorMeasured

/-! Persistent writes consume emitted actual raw reader/allocator plans.
Their preceding parent write plans, source/allocated/reversal charges and actual
parent emission prices remain exact. Added leaf emissions are forwarded. -/
namespace Blotto.BinaryWriteLeafPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryTraceDepth
open BinaryTracePlanMeasured (Plan)
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapPackedStore (Packed)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def readAtWithEmission (tape : List Bool) (pointer : Pointer) (depth : ℕ) :=
  BinaryNumericalReadbackPlan.finish (BinaryHeapReadPlan.readAt tape pointer depth)

theorem read_compat (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    (readAtWithEmission tape pointer depth).1 = BinaryHeapReadMeasured.readAt tape pointer depth := by
  rw [readAtWithEmission,BinaryNumericalReadbackPlan.finish_record,BinaryHeapReadPlan.read_refines]

theorem read_price (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    (readAtWithEmission tape pointer depth).2 ≤ 25*(readAtWithEmission tape pointer depth).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (BinaryHeapReadPlan.read_bound tape pointer depth)

def allocateAtWithEmission (heap : Heap) (cell : Cell) (depth : ℕ) :=
  BinaryNumericalReadbackPlan.finish (BinaryHeapAllocatorPlan.allocateAt heap cell depth)

theorem allocate_compat (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAtWithEmission heap cell depth).1 = BinaryHeapAllocationMeasured.allocateAt heap cell depth := by
  rw [allocateAtWithEmission,BinaryNumericalReadbackPlan.finish_record,BinaryHeapAllocatorPlan.allocate_refines]

theorem allocate_price (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAtWithEmission heap cell depth).2 ≤ 25*(allocateAtWithEmission heap cell depth).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (BinaryHeapAllocatorPlan.allocate_bound heap cell depth)

def patchPlanAt : Heap → Pointer → List Bool → List Bool → SignedWord → ℕ →
    ((Option (Pointer × Heap) × Plan) × Charge) × ℕ
  | heap,pointer,[],_,word,traceDepth =>
      let read := readAtWithEmission heap.tape pointer (traceDepth+1)
      let found := read.1
      match found.1.1 with
      | some (.leaf _) =>
          let allocated := allocateAtWithEmission heap (.leaf word) (traceDepth+1)
          let produced := allocated.1
          (((some produced.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 8])
            (.join (.block found.1.2) (.block produced.1.2))),found.2.add (produced.2.add ⟨4,4⟩)),read.2+allocated.2)
      | _ => (((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) (.block found.1.2)),found.2.add ⟨2,4⟩),read.2)
  | heap,pointer,_::ruler,address,word,traceDepth =>
      let read := readAtWithEmission heap.tape pointer (traceDepth+1)
      let found := read.1
      match found.1.1 with
      | some (.branch left right) =>
          let returned := if address.headD false then patchPlanAt heap right ruler address.tail word (traceDepth+1)
            else patchPlanAt heap left ruler address.tail word (traceDepth+1)
          let changed := returned.1
          match changed.1.1 with
          | none => (((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8])
              (.join (.block found.1.2) changed.1.2)),found.2.add (changed.2.add ⟨2,4⟩)),read.2+returned.2)
          | some later =>
              let cell := if address.headD false then Cell.branch left later.1 else Cell.branch later.1 right
              let allocated := allocateAtWithEmission later.2 cell (traceDepth+1)
              let produced := allocated.1
          (((some produced.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 16])
                (.join (.block found.1.2) (.join changed.1.2 (.block produced.1.2)))),
                found.2.add (changed.2.add (produced.2.add ⟨4,4⟩))),read.2+returned.2+allocated.2)
      | _ => (((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) (.block found.1.2)),found.2.add ⟨2,4⟩),read.2)

theorem patch_compat (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (depth : ℕ) :
    (patchPlanAt heap pointer ruler address word depth).1 = BinaryHeapWriteMeasured.patchPlanAt heap pointer ruler address word depth := by
  induction ruler generalizing heap pointer address depth with
  | nil =>
      simp only [patchPlanAt,BinaryHeapWriteMeasured.patchPlanAt,read_compat]
      cases hc : (BinaryHeapReadMeasured.readAt heap.tape pointer (depth+1)).1.1 with
      | none => rfl
      | some cell => cases cell <;> simp only [allocate_compat]
  | cons bit ruler ih =>
      simp only [patchPlanAt,BinaryHeapWriteMeasured.patchPlanAt,read_compat]
      cases hc : (BinaryHeapReadMeasured.readAt heap.tape pointer (depth+1)).1.1 with
      | none => rfl
      | some cell => cases cell with
        | leaf old => rfl
        | branch left right =>
            cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih]
            all_goals split <;> rename_i hChanged <;> simp only [hChanged,allocate_compat]

theorem patch_price (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (depth : ℕ) :
    (patchPlanAt heap pointer ruler address word depth).2 ≤
      25*BinaryTracePlanMeasured.payload (patchPlanAt heap pointer ruler address word depth).1.1.2 := by
  induction ruler generalizing heap pointer address depth with
  | nil =>
      have hr := read_price heap.tape pointer (depth+1)
      simp only [patchPlanAt]
      split
      · have ha := allocate_price heap (.leaf word) (depth+1)
        simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
        omega
      · simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega
  | cons bit ruler ih =>
      have hr := read_price heap.tape pointer (depth+1)
      simp only [patchPlanAt]
      split
      · rename_i left right hFound
        have hl := ih heap left address.tail (depth+1)
        have hh := ih heap right address.tail (depth+1)
        cases hd : address.headD false <;> simp only [hd,Bool.false_eq_true,ite_false,ite_true]
        all_goals
          split
          · simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega
          · rename_i later hLater
            have ha := allocate_price later.2 (if address.headD false then .branch left later.1 else .branch later.1 right) (depth+1)
            simp only [hd,Bool.false_eq_true,ite_false,ite_true] at ha
            simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
            omega
      · simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega

def writePlanAt {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : ((Packed depth × Plan) × (Charge × ℕ)) × ℕ :=
  let reversed := BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)
  let produced := patchPlanAt data.heap data.root data.ruler reversed.1.1 word (traceDepth+1)
  let executed := produced.1
  have hSome : executed.1.1.isSome := by
    dsimp only [executed,produced,reversed]
    rw [patch_compat,BinaryHeapWriteMeasured.patchPlanAt_data,BinaryPRGHeapAccessLifetime.patchWithTrace_erasure,
      BinarySeedCursorMeasured.reverseAt_erases,BinarySeedPreparationSpace.reverseWithTrace_result,
      List.reverseAux_eq,List.append_nil]
    exact data.write_isSome address word
  let result := executed.1.1.get hSome
  have hResult : (BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 = some result := by
    have h := (Option.some_get hSome).symm
    change executed.1.1 = some result at h
    simpa only [executed,produced,reversed,patch_compat,BinaryHeapWriteMeasured.patchPlanAt_data,BinaryPRGHeapAccessLifetime.patchWithTrace_erasure,
      BinarySeedCursorMeasured.reverseAt_erases,BinarySeedPreparationSpace.reverseWithTrace_result,
      List.reverseAux_eq,List.append_nil] using h
  let h := data.write_result address word result hResult
  (((⟨data.ruler,data.size,result.2,result.1,h.1,h.2⟩,
    .join (.block [.frames (traceDepth+2),.arrayAllocation 16]) (.join (.block reversed.1.2) executed.1.2)),
    (executed.2,reversed.2)),produced.2)

theorem write_compat {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) (word : SignedWord) (depth : ℕ) :
    (writePlanAt data address word depth).1 = BinaryHeapWriteMeasured.writePlanAt data address word depth := by
  simp only [writePlanAt,BinaryHeapWriteMeasured.writePlanAt,patch_compat]

theorem write_price {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) (word : SignedWord) (depth : ℕ) :
    (writePlanAt data address word depth).2 ≤ 25*BinaryTracePlanMeasured.payload (writePlanAt data address word depth).1.1.2 := by
  have h := patch_price data.heap data.root data.ruler
    (BinarySeedCursorMeasured.reverseAt address.bits [] (depth+1)).1.1 word (depth+1)
  simp only [writePlanAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  omega

def executePlanAt {depth : ℕ} (data : Packed depth) :
    List (BinaryPRGHeapWriteSequence.Change depth) → ℕ → ((Packed depth × Plan) × (Charge × ℕ)) × ℕ
  | [],traceDepth => (((data,.block [.frames (traceDepth+1),.arrayAllocation 8]),(⟨1,0⟩,0)),0)
  | change::rest,traceDepth =>
      let written := writePlanAt data change.1 change.2 (traceDepth+1)
      let current := written.1
      let returned := executePlanAt current.1.1 rest (traceDepth+1)
      let later := returned.1
      (((later.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 16]) (.join current.1.2 later.1.2)),
        (⟨current.2.1.work+later.2.1.work+4,current.2.1.allocatedBits+later.2.1.allocatedBits+4⟩,
          current.2.2+later.2.2)),written.2+returned.2)

theorem execute_plan_compat {width : ℕ} (data : Packed width) (changes : List (BinaryPRGHeapWriteSequence.Change width)) (depth : ℕ) :
    (executePlanAt data changes depth).1 = BinaryHeapWriteMeasured.executePlanAt data changes depth := by
  induction changes generalizing data depth with
  | nil => rfl
  | cons change rest ih => simp only [executePlanAt,BinaryHeapWriteMeasured.executePlanAt,write_compat,ih]

theorem execute_plan_price {width : ℕ} (data : Packed width) (changes : List (BinaryPRGHeapWriteSequence.Change width)) (depth : ℕ) :
    (executePlanAt data changes depth).2 ≤ 25*BinaryTracePlanMeasured.payload (executePlanAt data changes depth).1.1.2 := by
  induction changes generalizing data depth with
  | nil => simp only [executePlanAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega
  | cons change rest ih =>
      have hw := write_price data change.1 change.2 (depth+1)
      have hl := ih (writePlanAt data change.1 change.2 (depth+1)).1.1.1 (depth+1)
      simp only [executePlanAt,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
      omega

def executeAtMeasured {width : ℕ} (data : Packed width) (changes : List (BinaryPRGHeapWriteSequence.Change width)) (depth : ℕ) :=
  let produced := executePlanAt data changes depth
  let planned := produced.1
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  ((((planned.1.1,emitted.1),planned.2),emitted.2),produced.2)

theorem execute_compat {width : ℕ} (data : Packed width) (changes : List (BinaryPRGHeapWriteSequence.Change width)) (depth : ℕ) :
    (executeAtMeasured data changes depth).1 = BinaryHeapWriteMeasured.executeAtMeasured data changes depth := by
  simp only [executeAtMeasured,BinaryHeapWriteMeasured.executeAtMeasured,execute_plan_compat]

theorem execute_price {width : ℕ} (data : Packed width) (changes : List (BinaryPRGHeapWriteSequence.Change width)) (depth : ℕ) :
    (executeAtMeasured data changes depth).2 ≤ 25*(executeAtMeasured data changes depth).1.1.1.2.length := by
  have h := execute_plan_price data changes depth
  simpa only [executeAtMeasured,BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero] using h

end Blotto.BinaryWriteLeafPlan
