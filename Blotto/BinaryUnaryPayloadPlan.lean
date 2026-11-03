import Blotto.BinaryUnaryPayloadMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Unary delimiter/payload recursion constructs final-depth plans. The actual
payload reader emits once, preserving its full old data/trace/source record.
Native scalar/record/reference/allocator interpretation remains separate. -/
namespace Blotto.BinaryUnaryPayloadPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def findAt : List Bool → ℕ → (Option (List Bool) × Plan) × ℕ
  | [],depth => ((none,.block [.frames (depth+1),.arrayAllocation 8]),4)
  | true::rest,depth => ((some rest,.block [.frames (depth+1),.arrayAllocation 8]),4)
  | false::rest,depth =>
      let later := findAt rest (depth+2)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem find_refines (frame : List Bool) (depth : ℕ) :
    view (findAt frame depth) = offset depth (BinaryUnaryPayloadMeasured.find frame) := by
  induction frame generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [findAt,BinaryUnaryPayloadMeasured.find,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil] <;> rfl

theorem find_budget (frame : List Bool) (depth : ℕ) :
    Bounded (findAt frame depth).1.2 ∧ payload (findAt frame depth).1.2 ≤ (findAt frame depth).2 := by
  induction frame generalizing depth with
  | nil => simp [Bounded,findAt,nodes,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [Bounded,findAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢ <;> omega

def consumeAt : List Bool → List Bool → List Bool → ℕ → (Option (List Bool × List Bool) × Plan) × ℕ
  | [],_,_,depth => ((none,.block [.frames (depth+1),.arrayAllocation 8]),4)
  | true::_,bits,acc,depth => ((some (acc,bits),.block [.frames (depth+1),.arrayAllocation 8]),4)
  | false::_,[],_,depth => ((none,.block [.frames (depth+1),.arrayAllocation 8]),4)
  | false::ruler,bit::bits,acc,depth =>
      let later := consumeAt ruler bits (bit::acc) (depth+2)
      ((later.1.1,.join (.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem consume_refines (ruler bits acc : List Bool) (depth : ℕ) :
    view (consumeAt ruler bits acc depth) = offset depth (BinaryUnaryPayloadMeasured.consume ruler bits acc) := by
  induction ruler generalizing bits acc depth with
  | nil => rfl
  | cons mark ruler ih => cases mark with
    | true => rfl
    | false => cases bits with
      | nil => rfl
      | cons bit bits =>
          have h := ih bits (bit::acc) (depth+2)
          simp only [consumeAt,BinaryUnaryPayloadMeasured.consume,view,offset,denote,
            data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,
            under_append,under_compose,List.append_nil]
          rfl

theorem consume_budget (ruler bits acc : List Bool) (depth : ℕ) :
    Bounded (consumeAt ruler bits acc depth).1.2 ∧
      payload (consumeAt ruler bits acc depth).1.2 ≤ (consumeAt ruler bits acc depth).2 := by
  induction ruler generalizing bits acc depth with
  | nil => simp [Bounded,consumeAt,nodes,payload]
  | cons mark ruler ih => cases mark with
    | true => simp [Bounded,consumeAt,nodes,payload]
    | false => cases bits with
      | nil => simp [Bounded,consumeAt,nodes,payload]
      | cons bit bits =>
          have h := ih bits (bit::acc) (depth+2)
          simp only [Bounded,consumeAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
          omega

def readReversedAt (frame : List Bool) (depth : ℕ) : (Option (List Bool × List Bool) × Plan) × ℕ :=
  let found := findAt frame (depth+2)
  match found.1.1 with
  | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 16]) found.1.2),found.2+4)
  | some bits =>
      let copied := consumeAt frame bits [] (depth+2)
      ((copied.1.1,.join (.block [.frames (depth+2),.arrayAllocation 24]) (.join found.1.2 copied.1.2)),found.2+copied.2+8)

theorem readReversed_refines (frame : List Bool) (depth : ℕ) :
    view (readReversedAt frame depth) = offset depth (BinaryUnaryPayloadMeasured.readReversed frame) := by
  have hf := find_refines frame (depth+2)
  simp only [readReversedAt,BinaryUnaryPayloadMeasured.readReversed,data_refines hf]
  split
  · rename_i hNone
    simp only [view,offset,denote,hNone,trace_refines hf,charge_refines hf,wrap,combine,List.append_nil,under_append,under_compose]; rfl
  · rename_i bits hSome
    have hc := consume_refines frame bits [] (depth+2)
    simp only [view,offset,denote,hSome,data_refines hc,trace_refines hc,charge_refines hc,
      trace_refines hf,charge_refines hf,wrap,combine,List.append_nil,under_append,under_compose,List.append_assoc]
    rfl

theorem readReversed_budget (frame : List Bool) (depth : ℕ) :
    Bounded (readReversedAt frame depth).1.2 ∧
      payload (readReversedAt frame depth).1.2 ≤ (readReversedAt frame depth).2 := by
  have hf := find_budget frame (depth+2)
  unfold readReversedAt
  dsimp only
  split
  · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hf ⊢; omega
  · rename_i bits hSome
    have hc := consume_budget frame bits [] (depth+2)
    simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hf hc ⊢
    omega

def readAt (frame : List Bool) (depth : ℕ) : (Option (List Bool × List Bool) × Plan) × ℕ :=
  let raw := readReversedAt frame (depth+2)
  match raw.1.1 with
  | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 16]) raw.1.2),raw.2+4)
  | some parsed =>
      let reversed := BinarySeedCursorMeasured.reverseAt parsed.1 [] (depth+2)
      ((some (reversed.1.1,parsed.2),.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join raw.1.2 (.block reversed.1.2))),raw.2+reversed.2+8)

theorem read_refines (frame : List Bool) (depth : ℕ) :
    view (readAt frame depth) = offset depth (BinaryUnaryPayloadMeasured.read frame) := by
  have hr := readReversed_refines frame (depth+2)
  simp only [readAt,BinaryUnaryPayloadMeasured.read,data_refines hr]
  split
  · rename_i hNone
    simp only [view,offset,denote,hNone,trace_refines hr,charge_refines hr,wrap,combine,List.append_nil,under_append,under_compose]; rfl
  · rename_i parsed hSome
    simp only [view,offset,denote,hSome,trace_refines hr,charge_refines hr,
      BinarySeedCursorMeasured.reverseAt_erases,BinarySeedCursorMeasured.reverse_erases,
      BinarySeedCursorMeasured.reverseAt_work,BinarySeedCursorMeasured.reverse_work,
      wrap,combine,List.append_nil,under_append,under_compose,List.append_assoc]
    rfl

theorem read_budget (frame : List Bool) (depth : ℕ) :
    Bounded (readAt frame depth).1.2 ∧ payload (readAt frame depth).1.2 ≤ (readAt frame depth).2 := by
  have hr := readReversed_budget frame (depth+2)
  unfold readAt
  dsimp only
  split
  · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hr ⊢; omega
  · rename_i parsed hSome
    have ht := BinarySeedCursorMeasured.reverseAt_trace_length parsed.1 [] (depth+2)
    have hw := BinarySeedCursorMeasured.reverseAt_work parsed.1 [] (depth+2)
    rw [BinaryMidpointTapeLifetime.reverse_work] at hw
    simp only [Bounded,nodes,payload,List.length_cons,List.length_nil,ht] at hr ⊢
    omega

def readWithEmission (frame : List Bool) := finish (readAt frame 0)

theorem read_compat (frame : List Bool) :
    (readWithEmission frame).1 = BinaryUnaryPayloadMeasured.read frame :=
  BinaryNumericalReadbackPlan.finish_compat (read_refines frame 0)

theorem read_price (frame : List Bool) :
    (readWithEmission frame).2 ≤ 30*(readWithEmission frame).1.2 := by
  have h := BinaryNumericalReadbackPlan.finish_bound (readAt frame 0) (read_budget frame 0).1
  have hb := (read_budget frame 0).2
  have hp := nodes_pos (readAt frame 0).1.2
  have hn := (read_budget frame 0).1
  have hw : 4 ≤ (readAt frame 0).2 := by unfold readAt; dsimp only; split <;> dsimp only <;> omega
  simp only [readWithEmission,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at h ⊢
  omega

end Blotto.BinaryUnaryPayloadPlan
