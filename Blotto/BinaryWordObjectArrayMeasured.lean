import Blotto.BinaryHeapAllocationMeasured
import Blotto.BinaryWordObjectArrayLifetime

/-! Physical word-array construction returns its store and source-work charge
with a concrete trace plan. Only the outer requested entry emits the trace.
Old source data/traces/charges are exact; native scalar/reference/allocator
realization remains separate. -/
namespace Blotto.BinaryWordObjectArrayMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinaryWordObjectArray
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryTracePlanMeasured (Plan)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def encodePlanAt : List Pointer → ℕ → (List Bool × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | pointer::pointers,depth =>
      let field := BinaryHeapTapeMeasured.fieldAt pointer (depth+2)
      let later := encodePlanAt pointers (depth+2)
      let joined := BinaryHeapTapeMeasured.appendAt field.1.1 later.1.1 (depth+2)
      ((joined.1.1,.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.block field.1.2) (.join later.1.2 (.block joined.1.2)))),
        field.2.work+later.2+joined.2.work+4)

theorem encodePlanAt_data (pointers : List Pointer) (depth : ℕ) :
    (encodePlanAt pointers depth).1.1 = (BinaryReferenceVectorLifetime.encodeWithTrace pointers).1 := by
  induction pointers generalizing depth with
  | nil => rfl
  | cons pointer rest ih =>
      simp only [encodePlanAt,BinaryReferenceVectorLifetime.encodeWithTrace,
        BinaryHeapTapeMeasured.fieldAt_erases,BinaryHeapTapeMeasured.appendAt_erases,ih]

theorem encodePlanAt_trace (pointers : List Pointer) (depth : ℕ) :
    BinaryTracePlanMeasured.denote (encodePlanAt pointers depth).1.2 =
      under depth (BinaryReferenceVectorLifetime.encodeWithTrace pointers).2 := by
  induction pointers generalizing depth with
  | nil => rfl
  | cons pointer rest ih =>
      simp only [encodePlanAt,BinaryReferenceVectorLifetime.encodeWithTrace,BinaryTracePlanMeasured.denote,
        BinaryHeapTapeMeasured.fieldAt_erases,BinaryHeapTapeMeasured.appendAt_erases,
        encodePlanAt_data,ih,wrap,combine,under_append,under_compose,List.append_nil,List.append_assoc]
      rfl

theorem encodePlanAt_state (pointers : List Pointer) (depth : ℕ) :
    (encodePlanAt pointers depth).1.1 = BinaryReferenceVector.encode pointers := by
  rw [encodePlanAt_data]
  exact BinaryReferenceVectorLifetime.encode_state pointers

theorem encodePlanAt_work (pointers : List Pointer) (depth : ℕ) :
    (encodePlanAt pointers depth).2 = (BinaryWordObjectArrayLifetime.encodeWithWork pointers).2 := by
  induction pointers generalizing depth with
  | nil => rfl
  | cons pointer rest ih =>
      simp only [encodePlanAt,BinaryWordObjectArrayLifetime.encodeWithWork,
        BinaryHeapTapeMeasured.fieldAt_erases,BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_erasure,
        BinaryHeapTapeMeasured.fieldAt_charge,BinaryHeapTapeMeasured.appendAt_charge,
        encodePlanAt_state,BinaryWordObjectArrayLifetime.encodeWithWork_state,ih]

def encodeAtMeasured (pointers : List Pointer) (depth : ℕ) : ((List Bool × Trace) × ℕ) × ℕ :=
  let planned := encodePlanAt pointers depth
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def encodePointers (pointers : List Pointer) : (List Bool × Trace) × ℕ := (encodeAtMeasured pointers 0).1

theorem encode_erases (pointers : List Pointer) :
    (encodePointers pointers).1 = BinaryReferenceVectorLifetime.encodeWithTrace pointers := by
  simp only [encodePointers,encodeAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,
    encodePlanAt_data,encodePlanAt_trace,under_zero]

theorem encode_state (pointers : List Pointer) :
    (encodePointers pointers).1.1 = BinaryReferenceVector.encode pointers := by
  have h := congrArg Prod.fst (encode_erases pointers)
  exact h.trans (BinaryReferenceVectorLifetime.encode_state pointers)

theorem encode_data (pointers : List Pointer) :
    (encodePointers pointers).1.1 = (BinaryWordObjectArrayLifetime.encodeWithWork pointers).1 := by
  rw [encode_state,BinaryWordObjectArrayLifetime.encodeWithWork_state]

theorem encode_work (pointers : List Pointer) :
    (encodePointers pointers).2 = (BinaryWordObjectArrayLifetime.encodeWithWork pointers).2 := encodePlanAt_work pointers 0

def wordsPlanAt (heap : Heap) : List SignedWord → ℕ → ((List Pointer × Heap) × Plan) × ℕ
  | [],depth => ((([],heap),.block [.frames (depth+1),.arrayAllocation 8]),4)
  | word::rest,depth =>
      let allocated := BinaryHeapAllocationMeasured.allocateAt heap (.leaf word) (depth+2)
      let later := wordsPlanAt allocated.1.1.2 rest (depth+2)
      (((allocated.1.1.1::later.1.1.1,later.1.1.2),
        .join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 32])
          (.join (.block allocated.1.2) later.1.2)),allocated.2.work+later.2+8)

theorem wordsPlanAt_data (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    (wordsPlanAt heap items depth).1.1 = (BinaryWordObjectArrayLifetime.wordsWithTrace heap items).1 := by
  induction items generalizing heap depth with
  | nil => rfl
  | cons word rest ih =>
      simp only [wordsPlanAt,BinaryWordObjectArrayLifetime.wordsWithTrace,
        BinaryHeapAllocationMeasured.allocateAt_erases,ih]

theorem wordsPlanAt_trace (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    BinaryTracePlanMeasured.denote (wordsPlanAt heap items depth).1.2 =
      under depth (BinaryWordObjectArrayLifetime.wordsWithTrace heap items).2 := by
  induction items generalizing heap depth with
  | nil => rfl
  | cons word rest ih =>
      simp only [wordsPlanAt,BinaryWordObjectArrayLifetime.wordsWithTrace,BinaryTracePlanMeasured.denote,
        BinaryHeapAllocationMeasured.allocateAt_erases,wordsPlanAt_data,ih,
        wrapList,wrap,combine,under_append,under_compose,List.append_nil,List.append_assoc]
      rfl

theorem wordsPlanAt_state (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    (wordsPlanAt heap items depth).1.1 = allocateWords heap items := by
  rw [wordsPlanAt_data]
  exact BinaryWordObjectArrayLifetime.wordsWithTrace_state heap items

theorem wordsPlanAt_work (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    (wordsPlanAt heap items depth).2 = (BinaryWordObjectArrayLifetime.wordsWithWork heap items).2 := by
  induction items generalizing heap depth with
  | nil => rfl
  | cons word rest ih =>
      simp only [wordsPlanAt,BinaryWordObjectArrayLifetime.wordsWithWork,
        BinaryHeapAllocationMeasured.allocateAt_erases,BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure,
        BinaryHeapAllocationMeasured.allocateAt_charge,ih]

def wordsAtMeasured (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    (((List Pointer × Heap) × Trace) × ℕ) × ℕ :=
  let planned := wordsPlanAt heap items depth
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def words (heap : Heap) (items : List SignedWord) : ((List Pointer × Heap) × Trace) × ℕ :=
  (wordsAtMeasured heap items 0).1

theorem words_erases (heap : Heap) (items : List SignedWord) :
    (words heap items).1 = BinaryWordObjectArrayLifetime.wordsWithTrace heap items := by
  simp only [words,wordsAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,
    wordsPlanAt_data,wordsPlanAt_trace,under_zero]

theorem words_state (heap : Heap) (items : List SignedWord) :
    (words heap items).1.1 = allocateWords heap items := by
  have h := congrArg Prod.fst (words_erases heap items)
  exact h.trans (BinaryWordObjectArrayLifetime.wordsWithTrace_state heap items)

theorem words_data (heap : Heap) (items : List SignedWord) :
    (words heap items).1.1 = (BinaryWordObjectArrayLifetime.wordsWithWork heap items).1 := by
  rw [words_state,BinaryWordObjectArrayLifetime.wordsWithWork_state]

theorem words_work (heap : Heap) (items : List SignedWord) :
    (words heap items).2 = (BinaryWordObjectArrayLifetime.wordsWithWork heap items).2 := wordsPlanAt_work heap items 0

def preparePlan (items : List SignedWord) : (Store items.length × Plan) × ℕ :=
  let allocated := wordsPlanAt empty items 2
  let slots := encodePlanAt allocated.1.1.1 2
  have hState := wordsPlanAt_state empty items 2
  have h := allocate_contract empty items empty_valid
  ((⟨allocated.1.1.2,slots.1.1,(by rw [hState]; exact h.1),
    ⟨allocated.1.1.1,items,rfl,encodePlanAt_state _ _,(by rw [hState]; exact h.2.2.1)⟩⟩,
    .join (.block [.frames 2,.arrayAllocation 32]) (.join allocated.1.2 slots.1.2)),allocated.2+slots.2+8)

def prepareMeasured (items : List SignedWord) : ((Store items.length × Trace) × ℕ) × ℕ :=
  let planned := preparePlan items
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def prepare (items : List SignedWord) : (Store items.length × Trace) × ℕ := (prepareMeasured items).1

theorem prepare_state (items : List SignedWord) :
    (prepare items).1.1 = BinaryWordObjectArray.prepare items := by
  apply Store.ext
  · exact congrArg Prod.snd (wordsPlanAt_state empty items 2)
  · simp only [prepare,prepareMeasured,preparePlan,BinaryWordObjectArray.prepare,encodePlanAt_state,wordsPlanAt_state]

theorem prepare_erases (items : List SignedWord) :
    (prepare items).1 = BinaryWordObjectArrayLifetime.prepareWithTrace items := by
  apply Prod.ext
  · rw [prepare_state,BinaryWordObjectArrayLifetime.prepareWithTrace_state]
  · simp only [prepare,prepareMeasured,preparePlan,BinaryWordObjectArrayLifetime.prepareWithTrace,
      BinaryTracePlanMeasured.emit_data,List.append_nil,BinaryTracePlanMeasured.denote,
      wordsPlanAt_trace,encodePlanAt_trace,wordsPlanAt_data,wrap,combine,List.append_nil,List.append_assoc]

theorem prepare_work (items : List SignedWord) :
    (prepare items).2 = (BinaryWordObjectArrayLifetime.prepareWithWork items).2 := by
  simp only [prepare,prepareMeasured,preparePlan,BinaryWordObjectArrayLifetime.prepareWithWork,
    wordsPlanAt_work,wordsPlanAt_state,BinaryWordObjectArrayLifetime.wordsWithWork_state,encodePlanAt_work]

theorem prepare_bound (items : List SignedWord) :
    (prepare items).2 ≤ BinaryWordObjectArrayLifetime.workEnvelope items := by
  rw [prepare_work]
  exact BinaryWordObjectArrayLifetime.prepareWithWork_bound items

theorem prepare_all_prefix (items : List SignedWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare items).1.2 steps ≤
        borrowed+BinaryWordObjectArrayLifetime.envelope items ∧
      framePeak ((prepare items).1.2.take steps) ≤ BinaryWordObjectArrayLifetime.envelope items := by
  rw [prepare_erases]
  exact BinaryWordObjectArrayLifetime.all_prefix items borrowed steps

theorem encodePlanAt_budget (pointers : List Pointer) (depth : ℕ) :
    BinaryTracePlanMeasured.payload (encodePlanAt pointers depth).1.2+
      BinaryTracePlanMeasured.nodes (encodePlanAt pointers depth).1.2 ≤ 3*(encodePlanAt pointers depth).2 := by
  induction pointers generalizing depth with
  | nil => simp [encodePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes]
  | cons pointer rest ih =>
      have hl := ih (depth+2)
      have hf := BinaryHeapTapeMeasured.fieldAt_trace_work pointer (depth+2)
      have hj := BinaryHeapTapeMeasured.appendAt_trace_work
        (BinaryHeapTapeMeasured.fieldAt pointer (depth+2)).1.1 (encodePlanAt rest (depth+2)).1.1 (depth+2)
      simp only [encodePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
        List.length_cons,List.length_nil]
      omega

theorem wordsPlanAt_budget (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    BinaryTracePlanMeasured.payload (wordsPlanAt heap items depth).1.2+
      BinaryTracePlanMeasured.nodes (wordsPlanAt heap items depth).1.2 ≤ 2*(wordsPlanAt heap items depth).2 := by
  induction items generalizing heap depth with
  | nil => simp [wordsPlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes]
  | cons word rest ih =>
      have hl := ih (BinaryHeapAllocationMeasured.allocateAt heap (.leaf word) (depth+2)).1.1.2 (depth+2)
      have ha := BinaryHeapAllocationMeasured.allocateAt_trace_work heap (.leaf word) (depth+2)
      simp only [wordsPlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
        List.length_cons,List.length_nil]
      omega

theorem encodeAtMeasured_emission (pointers : List Pointer) (depth : ℕ) :
    (encodeAtMeasured pointers depth).2 ≤ 12*(encodeAtMeasured pointers depth).1.2 := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (encodePlanAt_budget pointers depth)
  change (BinaryTracePlanMeasured.emit (encodePlanAt pointers depth).1.2 []).2 ≤ 12*(encodePlanAt pointers depth).2
  omega

theorem wordsAtMeasured_emission (heap : Heap) (items : List SignedWord) (depth : ℕ) :
    (wordsAtMeasured heap items depth).2 ≤ 8*(wordsAtMeasured heap items depth).1.2 := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (wordsPlanAt_budget heap items depth)
  change (BinaryTracePlanMeasured.emit (wordsPlanAt heap items depth).1.2 []).2 ≤ 8*(wordsPlanAt heap items depth).2
  omega

theorem preparePlan_budget (items : List SignedWord) :
    BinaryTracePlanMeasured.payload (preparePlan items).1.2+
      BinaryTracePlanMeasured.nodes (preparePlan items).1.2 ≤ 3*(preparePlan items).2 := by
  have hw := wordsPlanAt_budget empty items 2
  have he := encodePlanAt_budget (wordsPlanAt empty items 2).1.1.1 2
  simp only [preparePlan,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
    List.length_cons,List.length_nil]
  omega

theorem prepareMeasured_emission (items : List SignedWord) :
    (prepareMeasured items).2 ≤ 12*(prepareMeasured items).1.2 := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (preparePlan_budget items)
  change (BinaryTracePlanMeasured.emit (preparePlan items).1.2 []).2 ≤ 12*(preparePlan items).2
  omega

theorem prepareMeasured_source_plus_emission (items : List SignedWord) :
    (prepareMeasured items).1.2+(prepareMeasured items).2 ≤ 13*(prepareMeasured items).1.2 := by
  have h := prepareMeasured_emission items
  omega

theorem prepare_emit_frames (items : List SignedWord) :
    BinaryTracePlanMeasured.emitFrames (preparePlan items).1.2 ≤ 3*(prepare items).2+1 := by
  have hf := BinaryTracePlanMeasured.emitFrames_bound (preparePlan items).1.2
  have hp := preparePlan_budget items
  change _ ≤ 3*(preparePlan items).2+1
  omega

theorem prepare_plan_references (items : List SignedWord) :
    BinaryTracePlanMeasured.planReferences (preparePlan items).1.2 ≤ 6*(prepare items).2 := by
  have hr := BinaryTracePlanMeasured.planReferences_bound (preparePlan items).1.2
  have hp := preparePlan_budget items
  change _ ≤ 6*(preparePlan items).2
  omega

theorem prepare_emission_width (items : List SignedWord) :
    binaryWordWidth (prepareMeasured items).2 ≤
      binaryWordWidth (12*BinaryWordObjectArrayLifetime.workEnvelope items) :=
  binaryWordWidth_mono ((prepareMeasured_emission items).trans (Nat.mul_le_mul_left 12 (prepare_bound items)))

end Blotto.BinaryWordObjectArrayMeasured
