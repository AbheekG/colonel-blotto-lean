import Blotto.BinaryPhysicalNumericalReadbackLifetime
import Blotto.BinaryCachePrefixPlan

/-! Physical numerical readback collects one final-depth plan through its list,
all-indices and pair wrappers, then emits once. Lookup and enumeration leaves
retain their prior scopes. Generic finishing lemmas apply to arbitrary old
ledgers; they do not execute denotation, size or reference observers. -/
namespace Blotto.BinaryNumericalReadbackPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryTracePlanMeasured
open BinaryCachePrefixPlan (Bounded block_bound)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def view {α β : Type*} (record : (α × Plan) × β) : (α × Trace) × β :=
  ((record.1.1,denote record.1.2),record.2)

def offset {α β : Type*} (depth : ℕ) (record : (α × Trace) × β) : (α × Trace) × β :=
  ((record.1.1,under depth record.1.2),record.2)

theorem data_refines {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β} {depth : ℕ}
    (h : view record = offset depth old) : record.1.1 = old.1.1 :=
  congrArg (fun out => out.1.1) h

theorem trace_refines {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β} {depth : ℕ}
    (h : view record = offset depth old) : denote record.1.2 = under depth old.1.2 :=
  congrArg (fun out => out.1.2) h

theorem charge_refines {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β} {depth : ℕ}
    (h : view record = offset depth old) : record.2 = old.2 := congrArg Prod.snd h

def finish {α β : Type*} (record : (α × Plan) × β) : ((α × Trace) × β) × ℕ :=
  let emitted := emitFull record.1.2 []
  (((record.1.1,emitted.1.1),record.2),emitted.1.2+emitted.2)

theorem finish_record {α β : Type*} (record : (α × Plan) × β) :
    (finish record).1 = view record := by
  simp only [finish,view,emitFull_erases,emit_data,List.append_nil]

theorem finish_compat {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β}
    (h : view record = offset 0 old) : (finish record).1 = old := by
  simpa only [finish_record,offset,under_zero] using h

theorem finish_bound {α β : Type*} (record : (α × Plan) × β) (h : Bounded record.1.2) :
    (finish record).2 ≤ 25*(finish record).1.1.2.length+5 := by
  have he := emitFull_total record.1.2 [] (5*payload record.1.2+1) (by unfold Bounded at h; omega)
  rw [finish_record]
  simp only [view,denote_length]
  dsimp only [finish] at he ⊢
  omega

def readManyAt {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    List (List Bool) → ℕ → (Option (List SignedWord) × Plan) × ℕ
  | [],depth => ((some [],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | index::rest,depth =>
      let current := BinaryWordObjectArrayAccess.getWithTrace store index
      let later := readManyAt store rest (depth+2)
      let result := match current.1,later.1.1 with
        | some word,some words => some (word::words)
        | _,_ => none
      ((result,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
        (.join (.shifted (depth+2) current.2) later.1.2)),later.2+1)

theorem readMany_refines {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    view (readManyAt store indices depth) =
      offset depth (BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork store indices) := by
  induction indices generalizing depth with
  | nil => rfl
  | cons index rest ih =>
      have h := ih (depth+2)
      simp only [readManyAt,BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,List.append_nil,under_append,under_compose]
      rfl

theorem readMany_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    Bounded (readManyAt store indices depth).1.2 := by
  induction indices generalizing depth with
  | nil => exact block_bound _
  | cons index rest ih =>
      have h := ih (depth+2)
      simp only [Bounded,readManyAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

theorem readMany_data {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    (readManyAt store indices depth).1.1 = (BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork store indices).1.1 :=
  data_refines (readMany_refines store indices depth)

theorem readMany_trace {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    denote (readManyAt store indices depth).1.2 = under depth (BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork store indices).1.2 :=
  trace_refines (readMany_refines store indices depth)

theorem readMany_work {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    (readManyAt store indices depth).2 = (BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork store indices).2 :=
  charge_refines (readMany_refines store indices depth)

def readAllAt {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) : (Option (List SignedWord) × Plan) × ℕ :=
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)
  let result := readManyAt store indices.1 (depth+2)
  ((result.1.1,.join (.block [.frames (depth+2),.arrayAllocation 32])
    (.join (.shifted (depth+2) indices.2) result.1.2)),result.2+1)

theorem readAll_refines {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    view (readAllAt store depth) = offset depth (BinaryPhysicalNumericalReadbackLifetime.readAllWithTraceAndWork store) := by
  simp only [readAllAt,BinaryPhysicalNumericalReadbackLifetime.readAllWithTraceAndWork,view,offset,denote,
    readMany_data,readMany_trace,readMany_work,wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem readAll_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    Bounded (readAllAt store depth).1.2 := by
  have h := readMany_bound store (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1 (depth+2)
  simp only [Bounded,readAllAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def pairAt {n : ℕ} (request : Request n) (depth : ℕ) :
    (Option (List SignedWord × List SignedWord) × Plan) × ℕ :=
  let lengths := readAllAt request.physical.lengthStore (depth+2)
  let poor := readAllAt request.physical.poorStore (depth+2)
  let result := do
    let lengthWords ← lengths.1.1
    let poorWords ← poor.1.1
    pure (lengthWords,poorWords)
  ((result,.join (.block [.frames (depth+2),.arrayAllocation 32]) (.join lengths.1.2 poor.1.2)),lengths.2+poor.2+1)

theorem pair_refines {n : ℕ} (request : Request n) (depth : ℕ) :
    view (pairAt request depth) = offset depth (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request) := by
  have hl := readAll_refines request.physical.lengthStore (depth+2)
  have hp := readAll_refines request.physical.poorStore (depth+2)
  simp only [pairAt,BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork,view,offset,denote,
    data_refines hl,trace_refines hl,charge_refines hl,data_refines hp,trace_refines hp,charge_refines hp,
    wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem pair_bound {n : ℕ} (request : Request n) (depth : ℕ) : Bounded (pairAt request depth).1.2 := by
  have hl := readAll_bound request.physical.lengthStore (depth+2)
  have hp := readAll_bound request.physical.poorStore (depth+2)
  simp only [Bounded,pairAt,nodes,payload,List.length_cons,List.length_nil] at hl hp ⊢
  omega

def readPairWithEmission {n : ℕ} (request : Request n) := finish (pairAt request 0)

theorem readPairWithEmission_compat {n : ℕ} (request : Request n) :
    (readPairWithEmission request).1 = BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request :=
  finish_compat (pair_refines request 0)

theorem readPairWithEmission_bound {n : ℕ} (request : Request n) :
    (readPairWithEmission request).2 ≤ 25*(readPairWithEmission request).1.1.2.length+5 :=
  finish_bound _ (pair_bound request 0)

end Blotto.BinaryNumericalReadbackPlan
