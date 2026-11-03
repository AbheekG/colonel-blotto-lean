import Blotto.BinaryTraceScalarReturnedBound
import Blotto.BinaryNumericalReadbackPlan
import Blotto.BinaryWrapperScalarWork

/-! Actual finishing records and all six wrapper emitters supply their own
scalar-addition work/usage ceilings. Generic returned-ledger polynomial transfer
and finite-call aggregation retain the canonical Boolean representation scope. -/
namespace Blotto.BinaryNumericalFinishScalarWork
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryPRGHeapTraceUsage
open BinaryTraceScalarReturnedBound
set_option autoImplicit false
set_option maxHeartbeats 1000000

def cost {α β : Type*} (record : (α × Plan) × β) : ℕ := BinaryTraceScalarWork.finishWork record.1.2 []

theorem bound {α β : Type*} (record : (α × Plan) × β) :
    cost record ≤ ceiling (BinaryNumericalReadbackPlan.finish record).2
      (usage (BinaryNumericalReadbackPlan.finish record).1.1.2) := by
  simpa only [cost,BinaryNumericalReadbackPlan.finish,charge] using finish_usage record.1.2 []

theorem width {α β : Type*} (record : (α × Plan) × β) :
    binaryWordWidth (cost record) ≤ binaryWordWidth (ceiling (BinaryNumericalReadbackPlan.finish record).2
      (usage (BinaryNumericalReadbackPlan.finish record).1.1.2)) := binaryWordWidth_mono (bound record)

theorem polynomial {α β : Type*} (record : (α × Plan) × β) :
    cost record ≤ 88*(BinaryNumericalReadbackPlan.finish record).2*
      ((BinaryNumericalReadbackPlan.finish record).2+usage (BinaryNumericalReadbackPlan.finish record).1.1.2+10) :=
  (bound record).trans (ceiling_polynomial _ _)

theorem all_prefix {α β : Type*} (record : (α × Plan) × β) (borrowed steps : ℕ) :
    borrowed+((BinaryTraceScalarAllocation.finish record.1.2 []).take steps).sum ≤
      borrowed+ceiling (BinaryNumericalReadbackPlan.finish record).2
        (usage (BinaryNumericalReadbackPlan.finish record).1.1.2) := by
  simpa only [BinaryNumericalReadbackPlan.finish,charge] using
    BinaryTraceScalarReturnedBound.all_prefix record.1.2 [] borrowed steps

theorem polynomial_transfer {α β : Type*} (produce : List Bool → (α × Plan) × β) (C d : ℕ)
    (h : ∀ frame,(BinaryNumericalReadbackPlan.finish (produce frame)).2+
      usage (BinaryNumericalReadbackPlan.finish (produce frame)).1.1.2 ≤ C*(frame.length+1)^d) :
    ∀ frame,cost (produce frame) ≤ 968*(C+1)^2*(frame.length+1)^(2*d) := by
  intro frame
  have hc := polynomial (produce frame)
  have ho := h frame
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  have hSum : (BinaryNumericalReadbackPlan.finish (produce frame)).2+
      usage (BinaryNumericalReadbackPlan.finish (produce frame)).1.1.2 ≤ (C+1)*(frame.length+1)^d := ho.trans (Nat.mul_le_mul_right _ (Nat.le_succ C))
  have hB : 1 ≤ (C+1)*(frame.length+1)^d := by nlinarith only [hOne]
  have hE : (BinaryNumericalReadbackPlan.finish (produce frame)).2 ≤ (C+1)*(frame.length+1)^d := by omega
  have hF : (BinaryNumericalReadbackPlan.finish (produce frame)).2+
      usage (BinaryNumericalReadbackPlan.finish (produce frame)).1.1.2+10 ≤ 11*((C+1)*(frame.length+1)^d) := by omega
  have hm := Nat.mul_le_mul hE hF
  calc
    _ ≤ 88*((BinaryNumericalReadbackPlan.finish (produce frame)).2*
        ((BinaryNumericalReadbackPlan.finish (produce frame)).2+usage (BinaryNumericalReadbackPlan.finish (produce frame)).1.1.2+10)) := by nlinarith only [hc]
    _ ≤ 88*(((C+1)*(frame.length+1)^d)*(11*((C+1)*(frame.length+1)^d))) := Nat.mul_le_mul_left 88 hm
    _ = 968*(C+1)^2*(frame.length+1)^(2*d) := by rw [Nat.mul_comm 2 d,pow_mul]; ring

theorem readPair_bound {n : ℕ} (request : BinaryPRGPhysicalRawRequestLifetime.Request n) :
    cost (BinaryNumericalReadbackPlan.pairAt request 0) ≤
      ceiling (BinaryNumericalReadbackPlan.readPairWithEmission request).2
        (usage (BinaryNumericalReadbackPlan.readPairWithEmission request).1.1.2) := bound _

theorem ceiling_add (E F U V : ℕ) : ceiling E U+ceiling F V ≤ ceiling (E+F) (U+V) := by
  have hwE := binaryWordWidth_mono (show E+U+8 ≤ E+F+(U+V)+8 by omega)
  have hwF := binaryWordWidth_mono (show F+V+8 ≤ E+F+(U+V)+8 by omega)
  have he := Nat.mul_le_mul_left (88*E) (Nat.add_le_add_right hwE 1)
  have hf := Nat.mul_le_mul_left (88*F) (Nat.add_le_add_right hwF 1)
  unfold ceiling
  nlinarith only [he,hf]

def aggregate (plans : List Plan) : ℕ := (plans.map (fun plan => BinaryTraceScalarWork.finishWork plan [])).sum

def emissionSum (plans : List Plan) : ℕ := (plans.map (fun plan => charge plan [])).sum

def frameSum (plans : List Plan) : ℕ := (plans.map (fun plan => framePeak (emitFull plan []).1.1)).sum

theorem aggregate_returned (plans : List Plan) : aggregate plans ≤ ceiling (emissionSum plans) (frameSum plans) := by
  induction plans with
  | nil => simp [aggregate,emissionSum,frameSum,ceiling]
  | cons plan rest ih =>
    have hh := finish_returned plan []
    have ha := ceiling_add (charge plan []) (emissionSum rest) (framePeak (emitFull plan []).1.1) (frameSum rest)
    simp only [aggregate,emissionSum,frameSum,List.map_cons,List.sum_cons] at *
    omega

theorem aggregate_polynomial (plans : List Plan) :
    aggregate plans ≤ 88*emissionSum plans*(emissionSum plans+frameSum plans+10) :=
  (aggregate_returned plans).trans (ceiling_polynomial _ _)

theorem one_returned (slots frames : ℕ) (trace : Trace) :
    BinaryWrapperScalarWork.one slots frames trace ≤ ceiling (BinaryWrapperEmission.one slots frames trace).2
      (usage (BinaryWrapperEmission.one slots frames trace).1) := by
  simpa only [BinaryWrapperScalarWork.one,BinaryWrapperEmission.one,charge] using finish_usage (.join (.block [.frames frames,.arrayAllocation slots]) (.shifted 2 trace)) []

theorem two_returned (slots frames : ℕ) (first second : Trace) :
    BinaryWrapperScalarWork.two slots frames first second ≤ ceiling (BinaryWrapperEmission.two slots frames first second).2
      (usage (BinaryWrapperEmission.two slots frames first second).1) := by
  simpa only [BinaryWrapperScalarWork.two,BinaryWrapperEmission.two,charge] using finish_usage (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) []

theorem listTwo_returned (allocated slots frames : ℕ) (first second : Trace) :
    BinaryWrapperScalarWork.listTwo allocated slots frames first second ≤ ceiling (BinaryWrapperEmission.listTwo allocated slots frames first second).2
      (usage (BinaryWrapperEmission.listTwo allocated slots frames first second).1) := by
  simpa only [BinaryWrapperScalarWork.listTwo,BinaryWrapperEmission.listTwo,charge] using finish_usage (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) []

theorem three_returned (slots frames : ℕ) (first second third : Trace) :
    BinaryWrapperScalarWork.three slots frames first second third ≤ ceiling (BinarySeedWrapperEmission.three slots frames first second third).2
      (usage (BinarySeedWrapperEmission.three slots frames first second third).1) := by
  simpa only [BinaryWrapperScalarWork.three,BinarySeedWrapperEmission.three,charge] using finish_usage (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []

theorem nested_returned (preparation store drawn : Trace) :
    BinaryWrapperScalarWork.nested preparation store drawn ≤ ceiling (BinarySeedWrapperEmission.nested preparation store drawn).2
      (usage (BinarySeedWrapperEmission.nested preparation store drawn).1) := by
  simpa only [BinaryWrapperScalarWork.nested,BinarySeedWrapperEmission.nested,charge] using finish_usage (.join (.block [.frames 2,.arrayAllocation 32]) (.join (.shifted 2 preparation) (.join (.block [.frames 4,.arrayAllocation 16]) (.join (.shifted 4 store) (.shifted 4 drawn))))) []

theorem listThree_returned (allocated slots frames : ℕ) (first second third : Trace) :
    BinaryWrapperScalarWork.listThree allocated slots frames first second third ≤ ceiling (BinaryInitialWrapperEmission.listThree allocated slots frames first second third).2
      (usage (BinaryInitialWrapperEmission.listThree allocated slots frames first second third).1) := by
  simpa only [BinaryWrapperScalarWork.listThree,BinaryInitialWrapperEmission.listThree,charge] using finish_usage (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []

def allocations (plans : List Plan) : List ℕ := plans.flatMap (fun plan => BinaryTraceScalarAllocation.finish plan [])

theorem allocations_sum (plans : List Plan) : (allocations plans).sum ≤ aggregate plans := by
  induction plans with
  | nil => rfl
  | cons plan rest ih =>
    have hh := BinaryTraceScalarAllocation.finish_sum plan []
    simp only [allocations,List.flatMap_cons,List.sum_append,aggregate,List.map_cons,List.sum_cons] at *
    omega

theorem aggregate_all_prefix (plans : List Plan) (borrowed steps : ℕ) :
    borrowed+((allocations plans).take steps).sum ≤ borrowed+ceiling (emissionSum plans) (frameSum plans) := by
  have hp := BinaryTraceScalarAllocation.take_sum (allocations plans) steps
  have ha := allocations_sum plans
  have hw := aggregate_returned plans
  omega

end Blotto.BinaryNumericalFinishScalarWork
