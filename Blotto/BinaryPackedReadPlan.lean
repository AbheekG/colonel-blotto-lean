import Blotto.BinaryHeapReadPlan
import Blotto.BinaryHeapPackedReadMeasured

/-! The reached physical lookup path and address reversal form one plan.
Its data, trace and source charges equal the old packed reader. Public read
emits once; no logical-tree witness or old work replay runs. -/
namespace Blotto.BinaryPackedReadPlan
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapPackedStore (Packed)
open BinaryNumericalReadbackPlan (view finish)
open BinaryHeapAllocatorPlan (data_eq trace_eq charge_eq)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def lookupAt : List Bool → Pointer → List Bool → List Bool → ℕ → (Option SignedWord × Plan) × Charge
  | tape,pointer,[],_,traceDepth =>
      let found := BinaryHeapReadPlan.readAt tape pointer (traceDepth+1)
      ((match found.1.1 with | some (.leaf word) => some word | _ => none,
        .join (.block [.frames (traceDepth+2),.arrayAllocation 8]) found.1.2),found.2.add ⟨2,4⟩)
  | tape,pointer,_::ruler,address,traceDepth =>
      let found := BinaryHeapReadPlan.readAt tape pointer (traceDepth+1)
      match found.1.1 with
      | some (.branch left right) =>
          let later := if address.headD false then lookupAt tape right ruler address.tail (traceDepth+1) else lookupAt tape left ruler address.tail (traceDepth+1)
          ((later.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) (.join found.1.2 later.1.2)),found.2.add (later.2.add ⟨4,4⟩))
      | _ => ((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) found.1.2),found.2.add ⟨2,4⟩)

theorem lookup_refines (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (depth : ℕ) :
    view (lookupAt tape pointer ruler address depth) = BinaryHeapPackedReadMeasured.lookupAt tape pointer ruler address depth := by
  induction ruler generalizing pointer address depth with
  | nil =>
      have hr := BinaryHeapReadPlan.read_refines tape pointer (depth+1)
      simp only [lookupAt,BinaryHeapPackedReadMeasured.lookupAt,view,denote,data_eq hr,trace_eq hr,charge_eq hr]
      rfl
  | cons bit ruler ih =>
      have hr := BinaryHeapReadPlan.read_refines tape pointer (depth+1)
      simp only [lookupAt,BinaryHeapPackedReadMeasured.lookupAt,data_eq hr]
      cases hc : (BinaryHeapReadMeasured.readAt tape pointer (depth+1)).1.1 with
      | none => simp only [view,denote,trace_eq hr,charge_eq hr]; rfl
      | some cell => cases cell with
        | leaf word => simp only [view,denote,trace_eq hr,charge_eq hr]; rfl
        | branch left right =>
            have hl := ih left address.tail (depth+1)
            have hh := ih right address.tail (depth+1)
            cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,
              view,denote,trace_eq hr,charge_eq hr,data_eq hl,trace_eq hl,charge_eq hl,
              data_eq hh,trace_eq hh,charge_eq hh] <;> rfl

theorem lookup_bound (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (depth : ℕ) :
    Bounded (lookupAt tape pointer ruler address depth).1.2 := by
  induction ruler generalizing pointer address depth with
  | nil =>
      have hr := BinaryHeapReadPlan.read_bound tape pointer (depth+1)
      simp only [lookupAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hr ⊢
      omega
  | cons bit ruler ih =>
      have hr := BinaryHeapReadPlan.read_bound tape pointer (depth+1)
      simp only [lookupAt]
      split
      · rename_i left right hc
        have hl := ih left address.tail (depth+1)
        have hh := ih right address.tail (depth+1)
        cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,
          Bounded,nodes,payload,List.length_cons,List.length_nil] at hr hl hh ⊢ <;> omega
      · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hr ⊢; omega

def readAt {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) : (SignedWord × Plan) × ℕ :=
  let reversed := BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)
  let executed := lookupAt data.heap.tape data.root data.ruler reversed.1.1 (traceDepth+1)
  have hSome : executed.1.1.isSome := by
    rw [data_eq (lookup_refines _ _ _ _ _),BinaryHeapPackedReadMeasured.lookupAt_data,BinarySeedCursorMeasured.reverseAt_erases,
      BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil]
    obtain ⟨tree,hTree⟩ := data.realized
    rw [BinaryPRGWordStoreHeapMachine.lookupWithWork_erasure,
      lookup_realizes hTree data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size])]
    rfl
  ((executed.1.1.get hSome,.join (.block [.frames (traceDepth+2),.arrayAllocation 16]) (.join (.block reversed.1.2) executed.1.2)),
    executed.2.work+reversed.2)

theorem read_refines {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :
    view (readAt data address depth) = BinaryHeapPackedReadMeasured.readAt data address depth := by
  have h := lookup_refines data.heap.tape data.root data.ruler
    (BinarySeedCursorMeasured.reverseAt address.bits [] (depth+1)).1.1 (depth+1)
  simp only [readAt,BinaryHeapPackedReadMeasured.readAt,view,denote,data_eq h,trace_eq h,charge_eq h]
  rfl

theorem read_bound {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) (depth : ℕ) :
    Bounded (readAt data address depth).1.2 := by
  have h := lookup_bound data.heap.tape data.root data.ruler
    (BinarySeedCursorMeasured.reverseAt address.bits [] (depth+1)).1.1 (depth+1)
  simp only [Bounded,readAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def readWithEmission {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) := finish (readAt data address 0)

theorem read_compat {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) :
    (readWithEmission data address).1 = BinaryHeapPackedReadMeasured.read data address := by
  rw [readWithEmission,BinaryNumericalReadbackPlan.finish_record,read_refines]
  rfl

theorem read_emission_bound {width : ℕ} (data : Packed width) (address : FixedBinaryWord width) :
    (readWithEmission data address).2 ≤ 25*(readWithEmission data address).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (read_bound data address 0)

end Blotto.BinaryPackedReadPlan
