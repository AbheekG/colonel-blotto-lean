import Blotto.BinaryTraceScalarWork

/-! Actual Boolean-adder allocated-bit records follow the emitter's source
order. Their total and every retained allocation-ledger prefix fit the derived
scalar work ceiling. Canonical operand formation and full physical native
allocation/record/reference/stack interpretation remain separate. -/
namespace Blotto.BinaryTraceScalarAllocation
open BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryTraceScalarWork
set_option autoImplicit false
set_option maxHeartbeats 1000000

def shiftAllocated (depth : ℕ) : Event → ℕ
  | .frames n => (add depth n).1.2
  | _ => 0

theorem shift_le_work (depth : ℕ) (event : Event) : shiftAllocated depth event ≤ shiftWork depth event := by
  cases event with
  | listAllocation n => exact Nat.le_refl _
  | arrayAllocation n => exact Nat.le_refl _
  | frames n => exact add_allocated depth n

def prepend : Trace → Trace → List ℕ
  | [],_ => []
  | _::rest,suffix => prepend rest suffix++[(add (BinaryTracePlanMeasured.prepend rest suffix).2 4).1.2]

theorem prepend_sum (events suffix : Trace) : (prepend events suffix).sum ≤ prependWork events suffix := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have ha := add_allocated (BinaryTracePlanMeasured.prepend rest suffix).2 4
    simp only [prepend,prependWork,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

def shifted (depth : ℕ) : Trace → Trace → List ℕ
  | [],_ => []
  | event::rest,suffix =>
    let later := prependShifted depth rest suffix
    shifted depth rest suffix++[shiftAllocated depth event,(add later.1.2 4).1.2,(add later.2 1).1.2]

theorem shifted_sum (depth : ℕ) (events suffix : Trace) : (shifted depth events suffix).sum ≤ shiftedWork depth events suffix := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have hs := shift_le_work depth event
    have ha := add_allocated (prependShifted depth rest suffix).1.2 4
    have hb := add_allocated (prependShifted depth rest suffix).2 1
    simp only [shifted,shiftedWork,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

def emit : Plan → Trace → List ℕ
  | .block events,suffix => prepend events suffix
  | .shifted depth events,suffix => shifted depth events suffix
  | .join first second,suffix =>
    let right := emitFull second suffix
    let left := emitFull first right.1.1
    emit second suffix++emit first right.1.1++
      [(add left.1.2 right.1.2).1.2,(add (left.1.2+right.1.2) 2).1.2,(add left.2 right.2).1.2]

theorem emit_sum (plan : Plan) (suffix : Trace) : (emit plan suffix).sum ≤ emitWork plan suffix := by
  induction plan generalizing suffix with
  | block events => exact prepend_sum events suffix
  | shifted depth events => exact shifted_sum depth events suffix
  | join first second ihFirst ihSecond =>
    have hf := ihFirst (emitFull second suffix).1.1
    have hs := ihSecond suffix
    have ha := add_allocated (emitFull first (emitFull second suffix).1.1).1.2 (emitFull second suffix).1.2
    have hb := add_allocated ((emitFull first (emitFull second suffix).1.1).1.2+(emitFull second suffix).1.2) 2
    have hc := add_allocated (emitFull first (emitFull second suffix).1.1).2 (emitFull second suffix).2
    simp only [emit,emitWork,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

def finish (plan : Plan) (suffix : Trace) : List ℕ :=
  let emitted := emitFull plan suffix
  emit plan suffix++[(add emitted.1.2 emitted.2).1.2]

theorem finish_sum (plan : Plan) (suffix : Trace) : (finish plan suffix).sum ≤ finishWork plan suffix := by
  have he := emit_sum plan suffix
  have ha := add_allocated (emitFull plan suffix).1.2 (emitFull plan suffix).2
  simp only [finish,finishWork,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

theorem take_sum (records : List ℕ) (steps : ℕ) : (records.take steps).sum ≤ records.sum := by
  induction records generalizing steps with
  | nil => simp
  | cons first rest ih =>
    cases steps with
    | zero => simp
    | succ steps => simpa only [List.take_succ_cons,List.sum_cons] using Nat.add_le_add_left (ih steps) first

theorem all_prefix (plan : Plan) (suffix : Trace) (borrowed steps : ℕ) :
    borrowed+((finish plan suffix).take steps).sum ≤ borrowed+88*(payload plan+nodes plan+1)*
      (binaryWordWidth (4*payload plan+2*nodes plan+planScalar plan+8)+1) := by
  have hp := take_sum (finish plan suffix) steps
  have hs := finish_sum plan suffix
  have hw := finish_closed plan suffix
  omega

end Blotto.BinaryTraceScalarAllocation
