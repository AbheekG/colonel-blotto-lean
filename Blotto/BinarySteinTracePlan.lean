import Blotto.BinarySteinGCDMeasured
import Blotto.BinaryWordCoinPrimitivesMeasured
import Blotto.BinaryNumericalReadbackPlan
import Blotto.BinaryPrimitiveTracePlan

/-! Actual Stein recursion collects final-depth plans. Scans and append use
existing final-depth leaves; signed difference and trim retain their existing
leaf scopes. No previous Stein loop is replayed. Old source reservations and
all old data/traces remain exact; native interpretation remains separate. -/
namespace Blotto.BinarySteinTracePlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem scan_data (bits : List Bool) (depth : ℕ) :
    (BooleanFreshSeedMeasured.scanAt bits depth).1.1 = (BooleanFreshSeedMeasured.scan bits).1.1 := by
  rw [BooleanFreshSeedMeasured.scanAt_erases,BooleanFreshSeedMeasured.scan_erases]

theorem scan_trace (bits : List Bool) (depth : ℕ) :
    (BooleanFreshSeedMeasured.scanAt bits depth).1.2 = under depth (BooleanFreshSeedMeasured.scan bits).1.2 := by
  rw [BooleanFreshSeedMeasured.scanAt_erases,BooleanFreshSeedMeasured.scan_erases]

def loopAt : List Bool → List Bool → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],first,second,depth =>
      let tested := BooleanFreshSeedMeasured.scanAt first (depth+2)
      ((if tested.1.1 then first else second,
        .join (.block [.frames (depth+2),.arrayAllocation 8]) (.block tested.1.2)),
        3*(first.length+1)+3*(second.length+1)+1)
  | _::ruler,first,second,depth =>
      let testedFirst := BooleanFreshSeedMeasured.scanAt first (depth+2)
      let firstPlan := .join (.block [.frames (depth+2),.arrayAllocation 8]) (.block testedFirst.1.2)
      let base := 3*(first.length+1)+3*(second.length+1)+4
      if testedFirst.1.1 then
        let testedSecond := BooleanFreshSeedMeasured.scanAt second (depth+2)
        let bothPlan := .join firstPlan (.block testedSecond.1.2)
        if testedSecond.1.1 then
          match first,second with
          | false::a,false::b =>
              let later := loopAt ruler a b (depth+1)
              ((false::later.1.1,.join bothPlan (.join (.block [.listAllocation 1]) later.1.2)),base+(3+later.2))
          | false::a,true::b =>
              let later := loopAt ruler a (true::b) (depth+1)
              ((later.1.1,.join bothPlan (.join (.block [.listAllocation 1]) later.1.2)),base+(2+later.2))
          | true::a,false::b =>
              let later := loopAt ruler (true::a) b (depth+1)
              ((later.1.1,.join bothPlan (.join (.block [.listAllocation 1]) later.1.2)),base+(2+later.2))
          | true::a,true::b =>
              let difference := BinarySignedMeasured.differenceTraced (true::a) (true::b)
              let later := if difference.1.1.negative then loopAt ruler (true::a) difference.1.1.bits.tail (depth+1)
                else loopAt ruler difference.1.1.bits.tail (true::b) (depth+1)
              ((later.1.1,.join bothPlan (.join (.block [.listAllocation 2])
                (.join (.shifted (depth+2) difference.1.2) later.1.2))),base+(difference.2+8+later.2))
          | _,_ => (([],bothPlan),base)
        else ((first,bothPlan),base)
      else ((second,firstPlan),base)

theorem loop_refines (ruler first second : List Bool) (depth : ℕ) :
    view (loopAt ruler first second depth) = offset depth (BinarySteinGCDMeasured.loop ruler first second) := by
  induction ruler generalizing first second depth with
  | nil =>
      simp only [loopAt,BinarySteinGCDMeasured.loop,view,offset,denote,scan_data,scan_trace,under_append,under_compose]
      rfl
  | cons unused ruler ih =>
      simp only [loopAt,BinarySteinGCDMeasured.loop,scan_data]
      by_cases ha : (BooleanFreshSeedMeasured.scan first).1.1 = true
      · simp only [ha,ite_true]
        by_cases hb : (BooleanFreshSeedMeasured.scan second).1.1 = true
        · simp only [hb,ite_true]
          cases first with
          | nil => simp only [view,offset,denote,scan_trace,under_append,under_compose,List.append_assoc]; rfl
          | cons a first => cases second with
            | nil => cases a <;> simp only [view,offset,denote,scan_trace,under_append,under_compose,List.append_assoc] <;> rfl
            | cons b second =>
                cases a <;> cases b <;> dsimp only
                · have h := ih first second (depth+1)
                  simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
                    scan_trace,under_append,under_compose,List.append_assoc]; rfl
                · have h := ih first (true::second) (depth+1)
                  simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
                    scan_trace,under_append,under_compose,List.append_assoc]; rfl
                · have h := ih (true::first) second (depth+1)
                  simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
                    scan_trace,under_append,under_compose,List.append_assoc]; rfl
                · split
                  · have h := ih (true::first)
                      (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail (depth+1)
                    simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
                      scan_trace,under_append,under_compose,List.append_assoc]; rfl
                  · have h := ih (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail
                      (true::second) (depth+1)
                    simp only [view,offset,denote,data_refines h,trace_refines h,charge_refines h,
                      scan_trace,under_append,under_compose,List.append_assoc]; rfl
        · simp only [hb,Bool.false_eq_true,ite_false,view,offset,denote,scan_trace,under_append,under_compose,List.append_assoc]; rfl
      · simp only [ha,Bool.false_eq_true,ite_false,view,offset,denote,scan_trace,under_append,under_compose,List.append_assoc]; rfl

theorem loop_budget (ruler first second : List Bool) (depth : ℕ) : Bounded (loopAt ruler first second depth).1.2 := by
  induction ruler generalizing first second depth with
  | nil => simp only [loopAt,Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
  | cons unused ruler ih =>
      unfold loopAt
      dsimp only
      split
      · split
        · cases first with
          | nil => simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
          | cons a first => cases second with
            | nil => cases a <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] <;> omega
            | cons b second =>
                cases a <;> cases b <;> dsimp only
                · have h := ih first second (depth+1)
                  simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢; omega
                · have h := ih first (true::second) (depth+1)
                  simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢; omega
                · have h := ih (true::first) second (depth+1)
                  simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢; omega
                · split
                  · have h := ih (true::first)
                      (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail (depth+1)
                    simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢; omega
                  · have h := ih (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail
                      (true::second) (depth+1)
                    simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢; omega
        · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
      · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega

def gcdAt (first second : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let ruler := BinaryWordCoinPrimitivesMeasured.appendAt first second (depth+2)
  let result := loopAt ruler.1.1 first second (depth+2)
  let trimmed := BinaryPrimitiveTracePlan.trimAt result.1.1 (depth+2)
  ((trimmed.1.1,.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join (.block ruler.1.2) (.join result.1.2 trimmed.1.2))),
    2*(first.length+second.length+1)+result.2+trimmed.2)

theorem gcd_refines (first second : List Bool) (depth : ℕ) :
    view (gcdAt first second depth) = offset depth (BinarySteinGCDMeasured.gcd first second) := by
  have h := loop_refines (BinaryPRGOutputLifetime.appendWithTrace first second).1 first second (depth+2)
  have ht := BinaryPrimitiveTracePlan.trim_refines
    (BinarySteinGCDMeasured.loop (BinaryPRGOutputLifetime.appendWithTrace first second).1 first second).1.1 (depth+2)
  simp only [gcdAt,BinarySteinGCDMeasured.gcd,view,offset,denote,
    data_refines ht,trace_refines ht,charge_refines ht,
    BinaryWordCoinPrimitivesMeasured.appendAt_erases,data_refines h,trace_refines h,charge_refines h,
    under_append,under_compose,List.append_assoc]
  rfl

theorem gcd_budget (first second : List Bool) (depth : ℕ) : Bounded (gcdAt first second depth).1.2 := by
  have h := loop_budget (BinaryWordCoinPrimitivesMeasured.appendAt first second (depth+2)).1.1 first second (depth+2)
  simp only [gcdAt,BinaryPrimitiveTracePlan.trimAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def gcd (first second : List Bool) := finish (gcdAt first second 0)

theorem gcd_compat (first second : List Bool) : (gcd first second).1 = BinarySteinGCDMeasured.gcd first second :=
  BinaryNumericalReadbackPlan.finish_compat (gcd_refines first second 0)

theorem gcd_price (first second : List Bool) : (gcd first second).2 ≤ 25*(gcd first second).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound (gcdAt first second 0) (gcd_budget first second 0)

end Blotto.BinarySteinTracePlan
