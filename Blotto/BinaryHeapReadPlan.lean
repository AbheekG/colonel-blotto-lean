import Blotto.BinaryHeapReadMeasured
import Blotto.BinaryHeapAllocatorPlan

/-! Physical skip/decode recursion builds a final-depth plan from reached
field, Boolean scan and predecessor results. Data and both old charges agree
exactly. Public read emits once; native observer interpretation stays separate. -/
namespace Blotto.BinaryHeapReadPlan
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryNumericalReadbackPlan (view finish)
open BinaryHeapAllocatorPlan (data_eq trace_eq charge_eq)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def decodeAt : List Bool → ℕ → (Option Cell × Plan) × Charge
  | false::negative::rest,depth =>
      let first := BinaryHeapTapeMeasured.readFieldAt rest (depth+1)
      match first.1.1 with
      | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.block first.1.2)),
          ⟨first.2.work+4,first.2.allocatedBits+4⟩)
      | some parsed =>
          let second := BinaryHeapTapeMeasured.readFieldAt parsed.2 (depth+1)
          ((second.1.1.map (fun later => .leaf ⟨negative,parsed.1,later.1⟩),
            .join (.block [.frames (depth+2),.arrayAllocation 16]) (.join (.block first.1.2) (.block second.1.2))),
            ⟨first.2.work+second.2.work+6,first.2.allocatedBits+second.2.allocatedBits+4⟩)
  | true::rest,depth =>
      let first := BinaryHeapTapeMeasured.readFieldAt rest (depth+1)
      match first.1.1 with
      | none => ((none,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.block first.1.2)),
          ⟨first.2.work+3,first.2.allocatedBits+4⟩)
      | some parsed =>
          let second := BinaryHeapTapeMeasured.readFieldAt parsed.2 (depth+1)
          ((second.1.1.map (fun later => .branch parsed.1 later.1),
            .join (.block [.frames (depth+2),.arrayAllocation 16]) (.join (.block first.1.2) (.block second.1.2))),
            ⟨first.2.work+second.2.work+5,first.2.allocatedBits+second.2.allocatedBits+4⟩)
  | _,depth => ((none,.block [.frames (depth+1),.arrayAllocation 8]),⟨2,0⟩)

theorem decode_refines (bits : List Bool) (depth : ℕ) :
    view (decodeAt bits depth) = BinaryHeapReadMeasured.decodeAt bits depth := by
  cases bits with
  | nil => rfl
  | cons tag rest => cases tag with
    | false => cases rest with
      | nil => rfl
      | cons negative rest =>
          simp only [decodeAt,BinaryHeapReadMeasured.decodeAt,view,denote]
          split <;> rename_i hParsed <;> simp only [hParsed,denote] <;> rfl
    | true =>
        simp only [decodeAt,BinaryHeapReadMeasured.decodeAt,view,denote]
        split <;> rename_i hParsed <;> simp only [hParsed,denote] <;> rfl

theorem decode_bound (bits : List Bool) (depth : ℕ) : Bounded (decodeAt bits depth).1.2 := by
  cases bits with
  | nil => exact block_bound _
  | cons tag rest => cases tag with
    | false => cases rest with
      | nil => exact block_bound _
      | cons negative rest =>
          simp only [decodeAt]
          split <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] <;> omega
    | true =>
        simp only [decodeAt]
        split <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] <;> omega

def skipAt (tape : List Bool) (pointer : Pointer) (width depth : ℕ) :
    (List Bool × Plan) × Charge :=
  let tested := BooleanFreshSeedMeasured.scanAt pointer (depth+1)
  if tested.1.1 then
    match tape with
    | [] => (([],.join (.block [.frames (depth+2),.arrayAllocation 8]) (.block tested.1.2)),⟨width+1+1,0⟩)
    | _::rest =>
        let decremented := BooleanFreshSeedMeasured.predecessorAt pointer (depth+1)
        let later := skipAt rest decremented.1.1 width (depth+1)
        ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8])
          (.join (.block tested.1.2) (.join (.block decremented.1.2) later.1.2))),
          ⟨width+1+decremented.2+later.2.work+3,width+later.2.allocatedBits⟩)
  else ((tape,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.block tested.1.2)),⟨width+1+1,0⟩)
termination_by tape.length

theorem skip_refines (tape : List Bool) (pointer : Pointer) (width depth : ℕ) :
    view (skipAt tape pointer width depth) = BinaryHeapReadMeasured.skipAt tape pointer width depth := by
  induction tape generalizing pointer width depth with
  | nil =>
      rw [skipAt,BinaryHeapReadMeasured.skipAt]
      split <;> rfl
  | cons bit rest ih =>
      rw [skipAt,BinaryHeapReadMeasured.skipAt]
      dsimp only
      split
      · have h := ih (BooleanFreshSeedMeasured.predecessorAt pointer (depth+1)).1.1 width (depth+1)
        simp only [view,denote,data_eq h,trace_eq h,charge_eq h]
        rfl
      · rfl

theorem skip_bound (tape : List Bool) (pointer : Pointer) (width depth : ℕ) :
    Bounded (skipAt tape pointer width depth).1.2 := by
  induction tape generalizing pointer width depth with
  | nil => rw [skipAt]; split <;> simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] <;> omega
  | cons bit rest ih =>
      rw [skipAt]
      dsimp only
      split
      · have h := ih (BooleanFreshSeedMeasured.predecessorAt pointer (depth+1)).1.1 width (depth+1)
        simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega
      · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]
        omega

def readAt (tape : List Bool) (pointer : Pointer) (depth : ℕ) : (Option Cell × Plan) × Charge :=
  let reached := skipAt tape pointer pointer.length (depth+1)
  let parsed := decodeAt reached.1.1 (depth+1)
  ((parsed.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join reached.1.2 parsed.1.2)),
    reached.2.add parsed.2)

theorem read_refines (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    view (readAt tape pointer depth) = BinaryHeapReadMeasured.readAt tape pointer depth := by
  have hs := skip_refines tape pointer pointer.length (depth+1)
  have hd := decode_refines (BinaryHeapReadMeasured.skipAt tape pointer pointer.length (depth+1)).1.1 (depth+1)
  simp only [readAt,BinaryHeapReadMeasured.readAt,view,denote,
    data_eq hs,trace_eq hs,charge_eq hs,data_eq hd,trace_eq hd,charge_eq hd]
  rfl

theorem read_bound (tape : List Bool) (pointer : Pointer) (depth : ℕ) : Bounded (readAt tape pointer depth).1.2 := by
  have hs := skip_bound tape pointer pointer.length (depth+1)
  have hd := decode_bound (skipAt tape pointer pointer.length (depth+1)).1.1 (depth+1)
  simp only [Bounded,readAt,nodes,payload,List.length_cons,List.length_nil] at hs hd ⊢
  omega

def readWithEmission (tape : List Bool) (pointer : Pointer) := finish (readAt tape pointer 0)

theorem read_compat (tape : List Bool) (pointer : Pointer) :
    (readWithEmission tape pointer).1 = BinaryHeapReadMeasured.read tape pointer := by
  rw [readWithEmission,BinaryNumericalReadbackPlan.finish_record,read_refines]
  rfl

theorem read_emission_bound (tape : List Bool) (pointer : Pointer) :
    (readWithEmission tape pointer).2 ≤ 25*(readWithEmission tape pointer).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (read_bound tape pointer 0)

end Blotto.BinaryHeapReadPlan
