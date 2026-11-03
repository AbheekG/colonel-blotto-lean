import Blotto.BinaryStoredDimensionHeaderMeasured
import Blotto.BinaryPositiveWordMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Header trimming and positive-word leading-zero control collect final-depth
plans. Header value/work-only map/append and final-depth reversal remain actual
leaves. Complete old records are exact; metadata/native costs remain explicit. -/
namespace Blotto.BinaryHeaderControlPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def dropAt : List Bool → ℕ → ((List Bool × ℕ) × Plan) × ℕ
  | [],depth => ((([],1),.block [.frames (depth+1),.arrayAllocation 8]),4)
  | true::rest,depth => (((true::rest,1),.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]),4)
  | false::rest,depth =>
      let later := dropAt rest (depth+2)
      (((later.1.1.1,later.1.1.2+1),.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem drop_refines (bits : List Bool) (depth : ℕ) :
    view (dropAt bits depth) = offset depth (BinaryStoredDimensionControlMeasured.drop bits) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [dropAt,BinaryStoredDimensionControlMeasured.drop,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,
        under_append,under_compose,List.append_nil] <;> rfl

theorem drop_budget (bits : List Bool) (depth : ℕ) :
    Bounded (dropAt bits depth).1.2 ∧ payload (dropAt bits depth).1.2 ≤ (dropAt bits depth).2 := by
  induction bits generalizing depth with
  | nil => simp [dropAt,Bounded,nodes,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [dropAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢ <;> omega

def trimAt (bits : List Bool) (depth : ℕ) : ((List Bool × ℕ) × Plan) × ℕ :=
  let front := BinarySeedCursorMeasured.reverseAt bits [] (depth+2)
  let dropped := dropAt front.1.1 (depth+2)
  let back := BinarySeedCursorMeasured.reverseAt dropped.1.1.1 [] (depth+2)
  let visits := 2*bits.length+3*dropped.1.1.2+2*back.1.1.length+2
  (((back.1.1,visits),.join (.block [.frames (depth+2*bits.length+4),.arrayAllocation 32])
    (.join (.block front.1.2) (.join dropped.1.2 (.block back.1.2)))),front.2+dropped.2+back.2+8)

theorem trim_refines (bits : List Bool) (depth : ℕ) :
    view (trimAt bits depth) = offset depth (BinaryStoredDimensionHeaderMeasured.trim bits) := by
  have hd := drop_refines (reverseWithTrace bits []).1 (depth+2)
  simp only [trimAt,BinaryStoredDimensionHeaderMeasured.trim,view,offset,denote,
    BinarySeedCursorMeasured.reverseAt_erases,BinarySeedCursorMeasured.reverse_erases,
    data_refines hd,trace_refines hd,charge_refines hd,
    BinarySeedCursorMeasured.reverseAt_work,BinarySeedCursorMeasured.reverse_work,
    wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem trim_budget (bits : List Bool) (depth : ℕ) :
    Bounded (trimAt bits depth).1.2 ∧ payload (trimAt bits depth).1.2 ≤ (trimAt bits depth).2 := by
  have hd := drop_budget (BinarySeedCursorMeasured.reverseAt bits [] (depth+2)).1.1 (depth+2)
  have hf := BinarySeedCursorMeasured.reverseAt_work bits [] (depth+2)
  have hb := BinarySeedCursorMeasured.reverseAt_work
    (dropAt (BinarySeedCursorMeasured.reverseAt bits [] (depth+2)).1.1 (depth+2)).1.1.1 [] (depth+2)
  rw [BinaryMidpointTapeLifetime.reverse_work] at hf hb
  simp only [trimAt,Bounded,nodes,payload,List.length_cons,List.length_nil,
    BinarySeedCursorMeasured.reverseAt_trace_length] at hd ⊢
  omega

def prepareAt (payload : List Bool) (depth : ℕ) : (BinaryStoredDimensionHeader.Header × Plan) × ℕ :=
  let reduced := trimAt payload (depth+2)
  let stored := if reduced.1.1.1 = [] then [false] else reduced.1.1.1
  let zeros := BinaryStoredDimensionHeaderMeasured.falseMap stored
  let joined := BinaryStoredDimensionHeaderMeasured.append zeros.1 (true::stored)
  let bytes := joined.1
  let visits := reduced.1.1.2+4*stored.length+3
  have hData : bytes = stored.map (fun _ => false) ++ true::stored := by
    dsimp only [bytes,joined]
    rw [BinaryStoredDimensionHeaderMeasured.append_data,BinaryStoredDimensionHeaderMeasured.falseMap_data]
  have hBytes : bytes = BinaryNatFrame.encode (BinaryBigEndian.littleValue payload) := by
    rw [hData]
    dsimp only [stored,reduced]
    rw [data_refines (trim_refines payload (depth+2)),
      BinaryStoredDimensionHeaderMeasured.trim_erases,BinaryStoredDimensionHeaderLifetime.trimWithTrace_state]
    exact BinaryStoredNatHeader.header_state payload
  have hVisits : visits ≤ 11*payload.length+12 := by
    dsimp only [visits,stored,reduced]
    rw [data_refines (trim_refines payload (depth+2)),
      BinaryStoredDimensionHeaderMeasured.trim_erases,BinaryStoredDimensionHeaderLifetime.trimWithTrace_state]
    exact BinaryStoredNatHeader.visits_bound payload
  ((⟨payload,bytes,hBytes,visits,hVisits⟩,
    .join (.block [.listAllocation (2*stored.length+2),
      .frames (depth+2*payload.length+stored.length+8),.arrayAllocation 32]) reduced.1.2),
    reduced.2+zeros.2+joined.2+8)

theorem prepare_refines (payload : List Bool) (depth : ℕ) :
    view (prepareAt payload depth) = offset depth (BinaryStoredDimensionHeaderMeasured.prepare payload) := by
  have h := trim_refines payload (depth+2)
  simp only [prepareAt,BinaryStoredDimensionHeaderMeasured.prepare,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,
    under_append,under_compose,List.append_nil]
  simp only [under,List.map_cons,List.map_nil,shiftEvent,Nat.add_assoc]
  rfl

theorem prepare_budget (payload : List Bool) (depth : ℕ) :
    Bounded (prepareAt payload depth).1.2 ∧ BinaryTracePlanMeasured.payload (prepareAt payload depth).1.2 ≤ (prepareAt payload depth).2 := by
  have h := trim_budget payload (depth+2)
  simp only [prepareAt,Bounded,nodes,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil] at h ⊢
  omega

def prepare (payload : List Bool) := finish (prepareAt payload 0)

theorem prepare_compat (payload : List Bool) :
    (prepare payload).1 = BinaryStoredDimensionHeaderMeasured.prepare payload :=
  BinaryNumericalReadbackPlan.finish_compat (prepare_refines payload 0)

theorem prepare_price (payload : List Bool) : (prepare payload).2 ≤ 30*(prepare payload).1.2 := by
  have hb := prepare_budget payload 0
  have he := BinaryNumericalReadbackPlan.finish_bound (prepareAt payload 0) hb.1
  have hw : 4 ≤ (prepareAt payload 0).2 := by unfold prepareAt; dsimp only; omega
  simp only [prepare,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

def positiveAt (bits : List Bool) (depth : ℕ) : (Option PositiveBinaryWord × Plan) × ℕ :=
  let trimmed := dropAt bits (depth+2)
  let parsed := match trimmed.1.1.1 with
    | true::tail => some (⟨tail⟩ : PositiveBinaryWord)
    | _ => none
  ((parsed,.join (.block [.frames (depth+2),.arrayAllocation 16]) trimmed.1.2),trimmed.2+4)

theorem positive_refines (bits : List Bool) (depth : ℕ) :
    view (positiveAt bits depth) = offset depth (BinaryPositiveWordMeasured.parse bits) := by
  have h := drop_refines bits (depth+2)
  simp only [positiveAt,BinaryPositiveWordMeasured.parse,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem positive_budget (bits : List Bool) (depth : ℕ) :
    Bounded (positiveAt bits depth).1.2 ∧ payload (positiveAt bits depth).1.2 ≤ (positiveAt bits depth).2 := by
  have h := drop_budget bits (depth+2)
  simp only [positiveAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def positive (bits : List Bool) := finish (positiveAt bits 0)

theorem positive_compat (bits : List Bool) : (positive bits).1 = BinaryPositiveWordMeasured.parse bits :=
  BinaryNumericalReadbackPlan.finish_compat (positive_refines bits 0)

theorem positive_price (bits : List Bool) : (positive bits).2 ≤ 30*(positive bits).1.2 := by
  have hb := positive_budget bits 0
  have he := BinaryNumericalReadbackPlan.finish_bound (positiveAt bits 0) hb.1
  have hw : 4 ≤ (positiveAt bits 0).2 := by unfold positiveAt; dsimp only; omega
  simp only [positive,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

end Blotto.BinaryHeaderControlPlan
