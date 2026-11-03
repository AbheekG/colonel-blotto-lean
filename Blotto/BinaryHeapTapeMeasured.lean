import Blotto.BinaryPRGHeapAllocationLifetime
import Blotto.BinaryReferenceVectorLifetime
import Blotto.BinaryTraceDepth

/-! Field encoding, field parsing and append return data, the established
source allocation trace and the established measured charge in one recursive
execution. Charge/trace observer evaluation and native reference/allocator
realization are separate from the Boolean tape source model. -/

namespace Blotto.BinaryHeapTapeMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryPRGWordStoreHeapMachine (Charge)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def fieldAt : List Bool → ℕ → (List Bool × Trace) × Charge
  | [],depth => (([false],[.frames (depth+1),.arrayAllocation 8,.listAllocation 1]),⟨2,1⟩)
  | bit::rest,depth =>
      let later := fieldAt rest (depth+1)
      ((true::bit::later.1.1,.frames (depth+1)::.arrayAllocation 8::.listAllocation 2::later.1.2),
        ⟨later.2.work+4,later.2.allocatedBits+2⟩)

theorem fieldAt_erases (bits : List Bool) (depth : ℕ) :
    (fieldAt bits depth).1 = ((BinaryPRGHeapPrimitiveLifetime.fieldWithTrace bits).1,
      under depth (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace bits).2) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      simp only [fieldAt,BinaryPRGHeapPrimitiveLifetime.fieldWithTrace,ih,under_append,under_compose]
      rfl

def field (bits : List Bool) : (List Bool × Trace) × Charge := fieldAt bits 0

theorem field_erases (bits : List Bool) :
    (field bits).1 = BinaryPRGHeapPrimitiveLifetime.fieldWithTrace bits := by
  rw [field,fieldAt_erases,under_zero]

theorem field_data (bits : List Bool) :
    (field bits).1.1 = (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).1 := by
  have h := congrArg Prod.fst (field_erases bits)
  exact h.trans (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_erasure bits)

theorem fieldAt_charge (bits : List Bool) (depth : ℕ) :
    (fieldAt bits depth).2 = (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).2 := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [fieldAt,BinaryPRGWordStoreHeapMachine.fieldWithWork,ih]

theorem field_charge (bits : List Bool) :
    (field bits).2 = (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).2 := fieldAt_charge bits 0

theorem field_price (bits : List Bool) :
    (field bits).2.work = 4*bits.length+2 ∧
      (field bits).2.allocatedBits = 2*bits.length+1 := by
  rw [field_charge]
  exact BinaryPRGWordStoreHeapMachine.fieldWithWork_price bits

theorem field_usage (bits : List Bool) : usage (field bits).1.2 ≤ 128*(bits.length+1) := by
  rw [field_erases]
  exact BinaryReferenceVectorLifetime.field_usage bits

def readFieldAt : List Bool → ℕ → (Option (List Bool × List Bool) × Trace) × Charge
  | false::rest,depth => ((some ([],rest),[.frames (depth+1),.arrayAllocation 8]),⟨2,0⟩)
  | true::bit::rest,depth =>
      let later := readFieldAt rest (depth+1)
      ((later.1.1.map (fun parsed => (bit::parsed.1,parsed.2)),
        .frames (depth+1)::.arrayAllocation 8::.listAllocation 1::later.1.2),
        ⟨later.2.work+4,later.2.allocatedBits+1⟩)
  | _,depth => ((none,[.frames (depth+1),.arrayAllocation 8]),⟨2,0⟩)

theorem readFieldAt_erases (bits : List Bool) (depth : ℕ) :
    (readFieldAt bits depth).1 = ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace bits).1,
      under depth (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace bits).2) := by
  induction bits using BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace.induct generalizing depth with
  | case1 rest => rfl
  | case2 bit rest ih =>
      simp only [readFieldAt,BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace,ih,under_append,under_compose]
      rfl
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => rfl
      | cons bit rest => cases bit with
        | false => exact False.elim (hFalse rest rfl)
        | true => cases rest with
          | nil => rfl
          | cons bit rest => exact False.elim (hTrue bit rest rfl)

def readField (bits : List Bool) : (Option (List Bool × List Bool) × Trace) × Charge := readFieldAt bits 0

theorem readField_erases (bits : List Bool) :
    (readField bits).1 = BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace bits := by
  rw [readField,readFieldAt_erases,under_zero]

theorem readField_data (bits : List Bool) :
    (readField bits).1.1 = (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).1 := by
  have h := congrArg Prod.fst (readField_erases bits)
  exact h.trans (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure bits)

theorem readFieldAt_charge (bits : List Bool) (depth : ℕ) :
    (readFieldAt bits depth).2 = (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).2 := by
  induction bits using BinaryPRGWordStoreHeapMachine.readFieldWithWork.induct generalizing depth with
  | case1 rest => rfl
  | case2 bit rest ih => simp only [readFieldAt,BinaryPRGWordStoreHeapMachine.readFieldWithWork,ih]
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => rfl
      | cons bit rest => cases bit with
        | false => exact False.elim (hFalse rest rfl)
        | true => cases rest with
          | nil => rfl
          | cons bit rest => exact False.elim (hTrue bit rest rfl)

theorem readField_charge (bits : List Bool) :
    (readField bits).2 = (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).2 := readFieldAt_charge bits 0

theorem readField_price (bits : List Bool) :
    (readField bits).2.work ≤ 4*bits.length+2 ∧
      (readField bits).2.allocatedBits ≤ bits.length := by
  rw [readField_charge]
  exact BinaryPRGWordStoreHeapMachine.readFieldWithWork_bounds bits

theorem readField_usage (bits : List Bool) :
    usage (readField bits).1.2 ≤ 33*(readField bits).2.work := by
  rw [readField_erases,readField_charge]
  exact BinaryReferenceVectorLifetime.readField_usage bits

def appendAt : List Bool → List Bool → ℕ → (List Bool × Trace) × Charge
  | [],suffix,depth => ((suffix,[.frames (depth+1),.arrayAllocation 8]),⟨1,0⟩)
  | bit::rest,suffix,depth =>
      let later := appendAt rest suffix (depth+1)
      ((bit::later.1.1,.frames (depth+1)::.arrayAllocation 8::.listAllocation 1::later.1.2),
        ⟨later.2.work+4,later.2.allocatedBits+1⟩)

theorem appendAt_erases (first second : List Bool) (depth : ℕ) :
    (appendAt first second depth).1 = ((BinaryPRGHeapPrimitiveLifetime.appendWithTrace first second).1,
      under depth (BinaryPRGHeapPrimitiveLifetime.appendWithTrace first second).2) := by
  induction first generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      simp only [appendAt,BinaryPRGHeapPrimitiveLifetime.appendWithTrace,ih,under_append,under_compose]
      rfl

def append (first second : List Bool) : (List Bool × Trace) × Charge := appendAt first second 0

theorem append_erases (first second : List Bool) :
    (append first second).1 = BinaryPRGHeapPrimitiveLifetime.appendWithTrace first second := by
  rw [append,appendAt_erases,under_zero]

theorem append_data (first second : List Bool) :
    (append first second).1.1 = (BinaryPRGWordStoreHeapMachine.appendWithWork first second).1 := by
  have h := congrArg Prod.fst (append_erases first second)
  exact h.trans (BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure first second)

theorem appendAt_charge (first second : List Bool) (depth : ℕ) :
    (appendAt first second depth).2 = (BinaryPRGWordStoreHeapMachine.appendWithWork first second).2 := by
  induction first generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [appendAt,BinaryPRGWordStoreHeapMachine.appendWithWork,ih]

theorem append_charge (first second : List Bool) :
    (append first second).2 = (BinaryPRGWordStoreHeapMachine.appendWithWork first second).2 :=
  appendAt_charge first second 0

theorem append_price (first second : List Bool) :
    (append first second).2.work = 4*first.length+1 ∧
      (append first second).2.allocatedBits = first.length := by
  rw [append_charge]
  exact BinaryPRGWordStoreHeapMachine.appendWithWork_price first second

theorem append_usage (first second : List Bool) :
    usage (append first second).1.2 ≤ 128*(first.length+1) := by
  rw [append_erases]
  exact BinaryReferenceVectorLifetime.append_usage first second

theorem fieldAt_trace_length (bits : List Bool) (depth : ℕ) :
    (fieldAt bits depth).1.2.length = 3*(bits.length+1) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [fieldAt,List.length_cons,ih]; omega

theorem fieldAt_frames (bits : List Bool) (depth : ℕ) :
    framePeak (fieldAt bits depth).1.2 ≤ depth+bits.length+1 := by
  induction bits generalizing depth with
  | nil => simp [fieldAt,framePeak]
  | cons bit rest ih =>
      have h := ih (depth+1)
      simp only [fieldAt,framePeak,List.length_cons] at h ⊢
      omega

theorem fieldAt_trace_work (bits : List Bool) (depth : ℕ) :
    (fieldAt bits depth).1.2.length ≤ 2*(fieldAt bits depth).2.work := by
  rw [fieldAt_trace_length,fieldAt_charge]
  have h := (BinaryPRGWordStoreHeapMachine.fieldWithWork_price bits).1
  omega

theorem readFieldAt_observers (bits : List Bool) (depth : ℕ) :
    (readFieldAt bits depth).1.2.length ≤ 2*(readFieldAt bits depth).2.work ∧
      framePeak (readFieldAt bits depth).1.2 ≤ depth+bits.length+1 := by
  induction bits using BinaryPRGWordStoreHeapMachine.readFieldWithWork.induct generalizing depth with
  | case1 rest => simp [readFieldAt,framePeak] <;> omega
  | case2 bit rest ih =>
      have h := ih (depth+1)
      simp only [readFieldAt,framePeak,List.length_cons] at h ⊢
      constructor <;> omega
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => simp [readFieldAt,framePeak]
      | cons bit rest => cases bit with
        | false => exact False.elim (hFalse rest rfl)
        | true => cases rest with
          | nil => simp [readFieldAt,framePeak] <;> omega
          | cons bit rest => exact False.elim (hTrue bit rest rfl)

theorem appendAt_trace_length (first second : List Bool) (depth : ℕ) :
    (appendAt first second depth).1.2.length = 3*first.length+2 := by
  induction first generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [appendAt,List.length_cons,ih]; omega

theorem appendAt_frames (first second : List Bool) (depth : ℕ) :
    framePeak (appendAt first second depth).1.2 ≤ depth+first.length+1 := by
  induction first generalizing depth with
  | nil => simp [appendAt,framePeak]
  | cons bit rest ih =>
      have h := ih (depth+1)
      simp only [appendAt,framePeak,List.length_cons] at h ⊢
      omega

theorem appendAt_trace_work (first second : List Bool) (depth : ℕ) :
    (appendAt first second depth).1.2.length ≤ 2*(appendAt first second depth).2.work := by
  rw [appendAt_trace_length,appendAt_charge]
  have h := (BinaryPRGWordStoreHeapMachine.appendWithWork_price first second).1
  omega

end Blotto.BinaryHeapTapeMeasured
