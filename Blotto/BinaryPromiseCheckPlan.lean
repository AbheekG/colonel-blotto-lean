import Blotto.BinaryPromiseControlPlan

/-! One actual ordered promise checker collects planned sums/opcodes and
short-circuit guard traces, then emits once. Only reached division work and
emission are charged. Exact preceding Boolean/trace/source records remain. -/
namespace Blotto.BinaryPromiseCheckPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
open BinaryPromiseControlPlan
set_option autoImplicit false
set_option maxHeartbeats 5000000

def fieldsAt {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : Record Bool :=
  let twice := opcodeAt .mul two input.a (depth+2)
  let tested := allAt (scaledAt twice.1.1.1 input.b) row (depth+2)
  (((tested.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 24])
    (.join twice.1.1.2 tested.1.1.2)),twice.1.2+tested.1.2+8),twice.2+tested.2)

theorem fields_refines {n : ℕ} (input : Input n) (row : List SignedWord) :
    Refines (fieldsAt input row) (BinaryPRGPromiseMeasured.fields input row) := by
  intro depth
  have ht := opcode_refines .mul two input.a (depth+2)
  have ha := all_refines (scaledAt (BinaryQuadraticMeasured.apply .mul two input.a).1.1 input.b)
    (BinaryPRGPromiseControlMeasured.scaled (BinaryQuadraticMeasured.apply .mul two input.a).1.1 input.b)
    (fun word => scaled_refines _ _ word) row (depth+2)
  simp only [fieldsAt,BinaryPRGPromiseMeasured.fields,view,offset,denote,
    data_refines ht,data_refines ha,trace_refines ht,trace_refines ha,charge_refines ht,charge_refines ha,
    wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem fields_safe {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : Safe (fieldsAt input row depth) := by
  have ht := opcode_safe .mul two input.a (depth+2)
  have ha := all_safe (scaledAt (opcodeAt .mul two input.a (depth+2)).1.1.1 input.b)
    (fun word => scaled_safe _ _ word) row (depth+2)
  simp only [fieldsAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at ht ha ⊢
  omega

def remainingAt {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : Record Bool :=
  let summed := sumAt row (depth+2)
  let later := andThenAt (equalAt summed.1.1.1 one) (fun _ =>
    andThenAt (positiveAt input.a) (fun _ =>
      andThenAt (positiveAt input.b) (fun _ =>
        andThenAt (comparisonAt input.b input.a) (fun _ => fieldsAt input row)))) (depth+2)
  (((later.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 24])
    (.join summed.1.1.2 later.1.1.2)),summed.1.2+later.1.2+8),summed.2+later.2)

theorem remaining_refines {n : ℕ} (input : Input n) (row : List SignedWord) :
    Refines (remainingAt input row) (BinaryPRGPromiseMeasured.remaining input row) := by
  have h3 := andThen_refines _ _ _ _ (comparison_refines input.b input.a) (fun _ => fields_refines input row)
  have h2 := andThen_refines _ _ _ _ (positive_refines input.b) (fun _ => h3)
  have h1 := andThen_refines _ _ _ _ (positive_refines input.a) (fun _ => h2)
  have h0 := andThen_refines _ _ _ _ (equal_refines (BinaryStoredWordSumMeasured.sum row).1.1 one) (fun _ => h1)
  intro depth
  have hs := sum_refines row (depth+2)
  have hl := h0 (depth+2)
  simp only [remainingAt,BinaryPRGPromiseMeasured.remaining,view,offset,denote,
    data_refines hs,data_refines hl,trace_refines hs,trace_refines hl,charge_refines hs,charge_refines hl,
    wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem remaining_safe {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : Safe (remainingAt input row depth) := by
  have h3 := andThen_safe _ _ (comparison_safe input.b input.a) (fun _ => fields_safe input row)
  have h2 := andThen_safe _ _ (positive_safe input.b) (fun _ => h3)
  have h1 := andThen_safe _ _ (positive_safe input.a) (fun _ => h2)
  have hs := sum_safe row (depth+2)
  have hl := andThen_safe _ _ (equal_safe (sumAt row (depth+2)).1.1.1 one) (fun _ => h1) (depth+2)
  simp only [remainingAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at hs hl ⊢
  omega

def checkRowsAt {n : ℕ} (input : Input n) (rows : List SignedWord) (depth : ℕ) : Record Bool :=
  let checked := andThenAt (allAt positiveAt rows) (fun _ => remainingAt input rows) (depth+2)
  (((checked.1.1.1,.join (.block [.listAllocation n,.frames (depth+n+4),.arrayAllocation 32]) checked.1.1.2),
    checked.1.2+4),checked.2)

theorem checkRows_refines {n : ℕ} (input : Input n) (rows : List SignedWord) :
    Refines (checkRowsAt input rows) (BinaryPRGPromiseMeasured.checkRows input rows) := by
  intro depth
  have h := andThen_refines _ _ _ _ (all_refines positiveAt _ positive_refines rows)
    (fun _ => remaining_refines input rows) (depth+2)
  simp only [checkRowsAt,BinaryPRGPromiseMeasured.checkRows,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,
    under_append,under_compose,List.append_nil]
  simp only [under,shiftEvent,List.map_cons,List.map_nil,Nat.add_assoc]
  rfl

theorem checkRows_safe {n : ℕ} (input : Input n) (rows : List SignedWord) (depth : ℕ) : Safe (checkRowsAt input rows depth) := by
  have h := andThen_safe _ _ (all_safe positiveAt positive_safe rows) (fun _ => remaining_safe input rows) (depth+2)
  simp only [checkRowsAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def checkRows {n : ℕ} (input : Input n) (rows : List SignedWord) : ((Bool × Trace) × ℕ) × ℕ :=
  let produced := checkRowsAt input rows 0
  let emitted := finish produced.1
  (emitted.1,produced.2+emitted.2)

theorem checkRows_compat {n : ℕ} (input : Input n) (rows : List SignedWord) :
    (checkRows input rows).1 = BinaryPRGPromiseMeasured.checkRows input rows := by
  exact BinaryNumericalReadbackPlan.finish_compat (checkRows_refines input rows 0)

theorem checkRows_price {n : ℕ} (input : Input n) (rows : List SignedWord) :
    (checkRows input rows).2 ≤ 4*(checkRows input rows).1.2+25*(checkRows input rows).1.1.2.length+5 := by
  have hs := checkRows_safe input rows 0
  have he := BinaryNumericalReadbackPlan.finish_bound (checkRowsAt input rows 0).1 hs.1
  simp only [Safe] at hs
  simp only [checkRows,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

end Blotto.BinaryPromiseCheckPlan
