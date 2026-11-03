import Blotto.BinaryRulerControlPlan
import Blotto.BinaryRulerPrecisionMeasured

/-! Alignment, comparison and precision execute final-depth child plans.
Only the actual append leaf emits a trace; no old ruler producer is replayed. -/
namespace Blotto.BinaryRulerPrecisionPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def shiftedAt (word : PositiveBinaryWord) (ruler : List Bool) (depth : ℕ) : (PositiveBinaryWord × Plan) × ℕ :=
  let zeros := BinaryRulerControlPlan.falseMapAt ruler (depth+2)
  let appended := BinaryWordCoinPrimitivesMeasured.appendAt word.tail zeros.1.1 (depth+2)
  ((⟨appended.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 24])
    (.join zeros.1.2 (.block appended.1.2))),zeros.2+appended.2+4)

theorem shifted_refines (word : PositiveBinaryWord) (ruler : List Bool) (depth : ℕ) :
    view (shiftedAt word ruler depth) = offset depth (BinaryRulerPrecisionMeasured.shifted word ruler) := by
  have h := BinaryRulerControlPlan.falseMap_refines ruler (depth+2)
  simp only [shiftedAt,BinaryRulerPrecisionMeasured.shifted,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,BinaryWordCoinPrimitivesMeasured.appendAt_erases,
    BinaryWordCoinPrimitivesMeasured.append_erases,BinaryWordCoinPrimitivesMeasured.appendAt_work,
    BinaryWordCoinPrimitivesMeasured.append_work,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem shifted_budget (word : PositiveBinaryWord) (ruler : List Bool) (depth : ℕ) :
    Bounded (shiftedAt word ruler depth).1.2 ∧
      payload (shiftedAt word ruler depth).1.2 ≤ (shiftedAt word ruler depth).2 := by
  have h := BinaryRulerControlPlan.falseMap_budget ruler (depth+2)
  simp only [shiftedAt,Bounded,nodes,payload,List.length_cons,List.length_nil,
    BinaryWordCoinPrimitivesMeasured.appendAt_trace_length,
    BinaryWordCoinPrimitivesMeasured.appendAt_work] at h ⊢
  omega

def leAt (a b : PositiveBinaryWord) (depth : ℕ) : (Bool × Plan) × ℕ :=
  let compared := BinaryRulerControlPlan.compareLengthAt a.tail b.tail (depth+2)
  match compared.1.1 with
  | .lt => ((true,.join (.block [.frames (depth+2),.arrayAllocation 16]) compared.1.2),compared.2+4)
  | .gt => ((false,.join (.block [.frames (depth+2),.arrayAllocation 16]) compared.1.2),compared.2+4)
  | .eq =>
      let scanned := BinaryRulerControlPlan.leScanAt a.bits b.bits (depth+2)
      ((scanned.1.1,.join (.block [.listAllocation 2,.frames (depth+2),.arrayAllocation 24])
        (.join compared.1.2 scanned.1.2)),compared.2+scanned.2+4)

theorem le_refines (a b : PositiveBinaryWord) (depth : ℕ) :
    view (leAt a b depth) = offset depth (BinaryRulerPrecisionMeasured.le a b) := by
  have hc := BinaryRulerControlPlan.compareLength_refines a.tail b.tail (depth+2)
  have hs := BinaryRulerControlPlan.leScan_refines a.bits b.bits (depth+2)
  simp only [leAt,BinaryRulerPrecisionMeasured.le,data_refines hc]
  cases (BinaryRulerControlMeasured.compareLength a.tail b.tail).1.1 <;>
    simp only [view,offset,denote,data_refines hs,trace_refines hc,trace_refines hs,
      charge_refines hc,charge_refines hs,wrapList,wrap,combine,under_append,under_compose,List.append_nil] <;> rfl

theorem le_budget (a b : PositiveBinaryWord) (depth : ℕ) :
    Bounded (leAt a b depth).1.2 ∧ payload (leAt a b depth).1.2 ≤ (leAt a b depth).2 := by
  have hc := BinaryRulerControlPlan.compareLength_budget a.tail b.tail (depth+2)
  have hs := BinaryRulerControlPlan.leScan_budget a.bits b.bits (depth+2)
  unfold leAt
  dsimp only
  split <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hc hs ⊢ <;> omega

def prepareAt (a b : PositiveBinaryWord) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let candidate := BinaryRulerControlPlan.differenceAt a.tail b.tail (depth+2)
  let aligned := shiftedAt b candidate.1.1 (depth+2)
  let compared := leAt a aligned.1.1 (depth+2)
  let ruler := if compared.1.1 then candidate.1.1 else true::candidate.1.1
  ((ruler,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 32])
    (.join candidate.1.2 (.join aligned.1.2 compared.1.2))),candidate.2+aligned.2+compared.2+8)

theorem prepare_refines (a b : PositiveBinaryWord) (depth : ℕ) :
    view (prepareAt a b depth) = offset depth (BinaryRulerPrecisionMeasured.prepare a b) := by
  have hc := BinaryRulerControlPlan.difference_refines a.tail b.tail (depth+2)
  have hs := shifted_refines b (BinaryRulerControlMeasured.difference a.tail b.tail).1.1 (depth+2)
  have hl := le_refines a (BinaryRulerPrecisionMeasured.shifted b
    (BinaryRulerControlMeasured.difference a.tail b.tail).1.1).1.1 (depth+2)
  simp only [prepareAt,BinaryRulerPrecisionMeasured.prepare,view,offset,denote,
    data_refines hc,data_refines hs,data_refines hl,trace_refines hc,trace_refines hs,trace_refines hl,
    charge_refines hc,charge_refines hs,charge_refines hl,wrapList,wrap,combine,
    under_append,under_compose,List.append_nil]
  rfl

theorem prepare_budget (a b : PositiveBinaryWord) (depth : ℕ) :
    Bounded (prepareAt a b depth).1.2 ∧ payload (prepareAt a b depth).1.2 ≤ (prepareAt a b depth).2 := by
  have hc := BinaryRulerControlPlan.difference_budget a.tail b.tail (depth+2)
  have hs := shifted_budget b (BinaryRulerControlPlan.differenceAt a.tail b.tail (depth+2)).1.1 (depth+2)
  have hl := le_budget a (shiftedAt b (BinaryRulerControlPlan.differenceAt a.tail b.tail (depth+2)).1.1 (depth+2)).1.1 (depth+2)
  simp only [prepareAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hc hs hl ⊢
  omega

def precisionAt (a b : PositiveBinaryWord) (depth : ℕ) : (ℕ × Plan) × ℕ :=
  let prepared := prepareAt a b (depth+2)
  let size := BinaryRulerPrecisionMeasured.length prepared.1.1
  ((size.1,.join (.block [.frames (depth+size.1+2),.arrayAllocation 16]) prepared.1.2),prepared.2+size.2+4)

theorem precision_refines (a b : PositiveBinaryWord) (depth : ℕ) :
    view (precisionAt a b depth) = offset depth (BinaryRulerPrecisionMeasured.precision a b) := by
  have h := prepare_refines a b (depth+2)
  simp only [precisionAt,BinaryRulerPrecisionMeasured.precision,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem precision_budget (a b : PositiveBinaryWord) (depth : ℕ) :
    Bounded (precisionAt a b depth).1.2 ∧ payload (precisionAt a b depth).1.2 ≤ (precisionAt a b depth).2 := by
  have h := prepare_budget a b (depth+2)
  simp only [precisionAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

end Blotto.BinaryRulerPrecisionPlan
