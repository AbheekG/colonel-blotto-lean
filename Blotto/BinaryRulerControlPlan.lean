import Blotto.BinaryRulerControlMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Actual Boolean ruler control collects final-depth plans without recursive
trace shifting. Complete old data and source work remain exact. -/
namespace Blotto.BinaryRulerControlPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def differenceAt : List Bool → List Bool → ℕ → (List Bool × Plan) × ℕ
  | bits,[],depth => ((bits,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | [],_::_,depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),2)
  | _::bits,_::other,depth =>
      let later := differenceAt bits other (depth+2)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem difference_refines (bits other : List Bool) (depth : ℕ) :
    view (differenceAt bits other depth) = offset depth (BinaryRulerControlMeasured.difference bits other) := by
  induction bits generalizing other depth with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other =>
        have h := ih other (depth+2)
        simp only [differenceAt,BinaryRulerControlMeasured.difference,view,offset,denote,
          data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil]
        rfl

theorem difference_budget (bits other : List Bool) (depth : ℕ) :
    Bounded (differenceAt bits other depth).1.2 ∧ payload (differenceAt bits other depth).1.2 ≤ (differenceAt bits other depth).2 := by
  induction bits generalizing other depth with
  | nil => cases other <;> simp [Bounded,differenceAt,nodes,payload]
  | cons bit bits ih => cases other with
    | nil => simp [Bounded,differenceAt,nodes,payload]
    | cons head other =>
        have h := ih other (depth+2)
        simp only [Bounded,differenceAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega

def compareLengthAt : List Bool → List Bool → ℕ → (Ordering × Plan) × ℕ
  | [],[],depth => ((.eq,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | [],_::_,depth => ((.lt,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | _::_,[],depth => ((.gt,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | _::bits,_::other,depth =>
      let later := compareLengthAt bits other (depth+2)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem compareLength_refines (bits other : List Bool) (depth : ℕ) :
    view (compareLengthAt bits other depth) = offset depth (BinaryRulerControlMeasured.compareLength bits other) := by
  induction bits generalizing other depth with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other =>
        have h := ih other (depth+2)
        simp only [compareLengthAt,BinaryRulerControlMeasured.compareLength,view,offset,denote,
          data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil]
        rfl

theorem compareLength_budget (bits other : List Bool) (depth : ℕ) :
    Bounded (compareLengthAt bits other depth).1.2 ∧
      payload (compareLengthAt bits other depth).1.2 ≤ (compareLengthAt bits other depth).2 := by
  induction bits generalizing other depth with
  | nil => cases other <;> simp [Bounded,compareLengthAt,nodes,payload]
  | cons bit bits ih => cases other with
    | nil => simp [Bounded,compareLengthAt,nodes,payload]
    | cons head other =>
        have h := ih other (depth+2)
        simp only [Bounded,compareLengthAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega

def leScanAt : List Bool → List Bool → ℕ → (Bool × Plan) × ℕ
  | [],_,depth => ((true,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | _::_,[],depth => ((false,.block [.frames (depth+1),.arrayAllocation 8]),2)
  | a::bits,b::other,depth =>
      if a=b then
        let later := leScanAt bits other (depth+2)
        ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+5)
      else ((!a,.block [.frames (depth+1),.arrayAllocation 8]),5)

theorem leScan_refines (bits other : List Bool) (depth : ℕ) :
    view (leScanAt bits other depth) = offset depth (BinaryRulerControlMeasured.leScan bits other) := by
  induction bits generalizing other depth with
  | nil => rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other =>
        have h := ih other (depth+2)
        simp only [leScanAt,BinaryRulerControlMeasured.leScan]
        split <;> simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
          wrap,combine,under_append,under_compose,List.append_nil] <;> rfl

theorem leScan_budget (bits other : List Bool) (depth : ℕ) :
    Bounded (leScanAt bits other depth).1.2 ∧ payload (leScanAt bits other depth).1.2 ≤ (leScanAt bits other depth).2 := by
  induction bits generalizing other depth with
  | nil => simp [Bounded,leScanAt,nodes,payload]
  | cons bit bits ih => cases other with
    | nil => simp [Bounded,leScanAt,nodes,payload]
    | cons head other =>
        have h := ih other (depth+2)
        simp only [leScanAt]
        split <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢ <;> omega

def falseMapAt : List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),2)
  | _::rest,depth =>
      let later := falseMapAt rest (depth+2)
      ((false::later.1.1,.join (.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem falseMap_refines (bits : List Bool) (depth : ℕ) :
    view (falseMapAt bits depth) = offset depth (BinaryRulerControlMeasured.falseMap bits) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      simp only [falseMapAt,BinaryRulerControlMeasured.falseMap,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,
        under_append,under_compose,List.append_nil]
      rfl

theorem falseMap_budget (bits : List Bool) (depth : ℕ) :
    Bounded (falseMapAt bits depth).1.2 ∧ payload (falseMapAt bits depth).1.2 ≤ (falseMapAt bits depth).2 := by
  induction bits generalizing depth with
  | nil => simp [Bounded,falseMapAt,nodes,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      simp only [Bounded,falseMapAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

end Blotto.BinaryRulerControlPlan
