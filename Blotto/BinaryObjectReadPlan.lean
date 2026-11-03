import Blotto.BinaryHeapReadPlan
import Blotto.BinaryWordObjectArrayAccessMeasured

/-! Reached reference fields and heap cells feed one physical object-lookup
plan. EOF and old source work are exact. The public lookup emits once, retaining
all old records; native length/reservation/reference prices remain separate. -/
namespace Blotto.BinaryObjectReadPlan
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryHeapAllocatorPlan (data_eq trace_eq charge_eq)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem field_value (tape : List Bool) (depth : ℕ) :
    (BinaryHeapTapeMeasured.readFieldAt tape depth).1.1 =
      (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).1 := by
  have h := congrArg Prod.fst (BinaryHeapTapeMeasured.readFieldAt_erases tape depth)
  exact h

theorem zero_field_value (tape : List Bool) :
    (BinaryHeapTapeMeasured.readField tape).1.1 =
      (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).1 :=
  congrArg Prod.fst (BinaryHeapTapeMeasured.readField_erases tape)

def slotAt (tape index : List Bool) (depth : ℕ) : (Option Pointer × Plan) × ℕ :=
  let field := BinaryHeapTapeMeasured.readFieldAt tape (depth+2)
  match hField : field.1.1 with
  | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 16]) (.block field.1.2)),field.2.work+4)
  | some parsed =>
      let tested := BooleanFreshSeedMeasured.scanAt index (depth+2)
      if tested.1.1 = true then
        let decremented := BooleanFreshSeedMeasured.predecessorAt index (depth+2)
        let later := slotAt parsed.2 decremented.1.1 (depth+2)
        ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 48])
          (.join (.block field.1.2) (.join (.block tested.1.2) (.join (.block decremented.1.2) later.1.2)))),
          field.2.work+(index.length+1)+decremented.2+later.2+8)
      else ((some parsed.1,.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.block field.1.2) (.block tested.1.2))),field.2.work+(index.length+1)+8)
termination_by tape.length
decreasing_by
  apply BinaryReferenceVector.readField_strict tape parsed
  exact (BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
    ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans
      ((field_value tape (depth+2)).symm.trans hField))

theorem slot_refines (tape index : List Bool) (depth : ℕ) :
    view (slotAt tape index depth) = offset depth (BinaryReferenceReadMeasured.read tape index) := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index depth,
      view (slotAt tape index depth) = offset depth (BinaryReferenceReadMeasured.read tape index) := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index depth
        rw [slotAt,BinaryReferenceReadMeasured.read]
        dsimp only
        simp only [field_value,zero_field_value,BinaryHeapTapeMeasured.readFieldAt_erases,BinaryHeapTapeMeasured.readField_erases,
          BinaryHeapTapeMeasured.readFieldAt_charge,BinaryHeapTapeMeasured.readField_charge]
        rw [field_value,zero_field_value]
        cases hp : (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).1 with
        | none =>
            simp only [view,offset,denote,wrap,combine,List.append_nil,under_append,under_compose]
            rfl
        | some parsed =>
            have hLess := BinaryReferenceVector.readField_strict tape parsed
              ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
                ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans hp))
            simp only [BooleanFreshSeedMeasured.scanAt_erases,BooleanFreshSeedMeasured.scan_erases,
              BooleanFreshSeedMeasured.predecessorAt_erases,BooleanFreshSeedMeasured.predecessor_erases,
              BooleanFreshSeedMeasured.predecessorAt_work,BooleanFreshSeedMeasured.predecessor_work]
            split
            · have hl := ih _ (by omega) parsed.2 rfl
                (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index).1 (depth+2)
              simp only [view,offset,denote,data_refines hl,trace_refines hl,charge_refines hl,
                wrap,combine,List.append_nil,under_append,under_compose,List.append_assoc]
              rfl
            · simp only [view,offset,denote,wrap,combine,List.append_nil,under_append,under_compose]
              rfl
  exact hAll _ tape rfl index depth

theorem slot_bound (tape index : List Bool) (depth : ℕ) : Bounded (slotAt tape index depth).1.2 := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index depth,
      Bounded (slotAt tape index depth).1.2 := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index depth
        rw [slotAt]
        dsimp only
        split
        · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
        · rename_i parsed hp
          have hLess := BinaryReferenceVector.readField_strict tape parsed
            ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
              ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans
                ((field_value tape (depth+2)).symm.trans hp)))
          split
          · have hl := ih _ (by omega) parsed.2 rfl
              (BooleanFreshSeedMeasured.predecessorAt index (depth+2)).1.1 (depth+2)
            simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hl ⊢
            omega
          · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
  exact hAll _ tape rfl index depth

def getAt {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) (depth : ℕ) :
    (Option SignedWord × Plan) × ℕ :=
  let slot := slotAt store.slots index (depth+2)
  match slot.1.1 with
  | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 16]) slot.1.2),slot.2+4)
  | some pointer =>
      let object := BinaryHeapReadPlan.readAt store.heap.tape pointer (depth+2)
      ((match object.1.1 with | some (.leaf word) => some word | _ => none,
        .join (.block [.frames (depth+2),.arrayAllocation 48]) (.join slot.1.2 object.1.2)),slot.2+object.2.work+4)

theorem get_refines {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) (depth : ℕ) :
    view (getAt store index depth) = offset depth (BinaryWordObjectArrayAccessMeasured.get store index) := by
  have hs := slot_refines store.slots index (depth+2)
  simp only [getAt,BinaryWordObjectArrayAccessMeasured.get,data_refines hs]
  split
  · rename_i hp
    simp only [hp,view,offset,denote,trace_refines hs,charge_refines hs,wrap,combine,List.append_nil,under_append,under_compose]
    rfl
  · rename_i pointer hp
    have hr := BinaryHeapReadPlan.read_refines store.heap.tape pointer (depth+2)
    simp only [hp,view,offset,denote,trace_refines hs,charge_refines hs,data_eq hr,trace_eq hr,charge_eq hr,
      BinaryHeapReadMeasured.readAt_erases,BinaryHeapReadMeasured.read_erases,
      BinaryHeapReadMeasured.readAt_charge,BinaryHeapReadMeasured.read_charge,
      wrap,combine,List.append_nil,under_append,under_compose]
    rfl

theorem get_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) (depth : ℕ) :
    Bounded (getAt store index depth).1.2 := by
  have hs := slot_bound store.slots index (depth+2)
  simp only [getAt]
  split
  · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hs ⊢; omega
  · rename_i pointer hp
    have hr := BinaryHeapReadPlan.read_bound store.heap.tape pointer (depth+2)
    simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hs hr ⊢
    omega

def getWithEmission {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) := finish (getAt store index 0)

theorem get_compat {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) :
    (getWithEmission store index).1 = BinaryWordObjectArrayAccessMeasured.get store index :=
  BinaryNumericalReadbackPlan.finish_compat (get_refines store index 0)

theorem get_emission_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) :
    (getWithEmission store index).2 ≤ 25*(getWithEmission store index).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (get_bound store index 0)

end Blotto.BinaryObjectReadPlan
