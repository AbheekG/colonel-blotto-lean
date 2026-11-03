import Blotto.BinaryTracePlanMeasured
import Blotto.BinaryArithmeticMeasured
import Blotto.BinaryPRGHeapTraceUsage

/-! The actual emitter's natural additions have a concrete Boolean-adder
interpretation on their canonical little-endian operand words. Prices include
the checked adder's Boolean work. Forming these representation words, host Nat
layout, references and allocator/GC interpretation remain separate. -/
namespace Blotto.BinaryTraceScalarWork
open BinarySeedPreparationSpace BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 1000000

def add (first second : ℕ) :=
  BinaryArithmeticMeasured.add (BinaryPayload.bits (binaryWordWidth first) first)
    (BinaryPayload.bits (binaryWordWidth second) second)

theorem add_value (first second : ℕ) : BinaryBigEndian.littleValue (add first second).1.1 = first+second := by
  rw [add,BinaryArithmeticMeasured.add_data,BinaryAddition.add_value]
  rw [BinaryBigEndian.littleValue_decode,BinaryBigEndian.littleValue_decode,
    BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth first),
    BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth second)]

theorem add_work (first second : ℕ) :
    (add first second).2 = 22*(max (binaryWordWidth first) (binaryWordWidth second)+1) := by
  simp only [add,BinaryArithmeticMeasured.add,BinaryPayload.bits_length]

theorem add_bound (first second Q : ℕ) (hf : first ≤ Q) (hs : second ≤ Q) :
    (add first second).2 ≤ 22*(binaryWordWidth Q+1) := by
  have hfw := binaryWordWidth_mono hf
  have hsw := binaryWordWidth_mono hs
  rw [add_work]
  omega

theorem add_output_width (first second Q : ℕ) (hf : first ≤ Q) (hs : second ≤ Q) :
    (add first second).1.1.length ≤ binaryWordWidth Q+1 := by
  have h := BinaryAddition.add_length (BinaryPayload.bits (binaryWordWidth first) first)
    (BinaryPayload.bits (binaryWordWidth second) second)
  have hfw := binaryWordWidth_mono hf
  have hsw := binaryWordWidth_mono hs
  simp only [BinaryPayload.bits_length] at h
  simp only [add,BinaryArithmeticMeasured.add_data]
  omega

theorem add_allocated (first second : ℕ) : (add first second).1.2 ≤ (add first second).2 := by
  have h := BinaryArithmeticAllocation.addLoopAllocated_bound
    (BinaryPayload.bits (binaryWordWidth first) first) (BinaryPayload.bits (binaryWordWidth second) second) false []
  simp only [BinaryPayload.bits_length,List.length_nil,Nat.add_zero] at h
  simp only [add,BinaryArithmeticMeasured.add,BinaryArithmeticAllocation.addWithAllocation_refines,
    BinaryPayload.bits_length]
  omega

def eventScalar : Event → ℕ
  | .listAllocation n => n
  | .arrayAllocation n => n
  | .frames n => n

def traceScalar : Trace → ℕ
  | [] => 0
  | event::rest => max (eventScalar event) (traceScalar rest)

theorem traceScalar_usage (trace : Trace) : traceScalar trace ≤ BinaryPRGHeapTraceUsage.usage trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp only [traceScalar,eventScalar,BinaryPRGHeapTraceUsage.usage,
      BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak] at ih ⊢ <;> omega

def planScalar : Plan → ℕ
  | .block events => traceScalar events
  | .join first second => max (planScalar first) (planScalar second)
  | .shifted depth events => depth+traceScalar events

def shiftWork (depth : ℕ) : Event → ℕ
  | .frames n => (add depth n).2
  | _ => 0

theorem shift_bound (depth : ℕ) (event : Event) (Q : ℕ) (h : depth+eventScalar event ≤ Q) :
    shiftWork depth event ≤ 22*(binaryWordWidth Q+1) := by
  cases event with
  | listAllocation n => exact Nat.zero_le _
  | arrayAllocation n => exact Nat.zero_le _
  | frames n =>
    exact add_bound depth n Q (by simp only [eventScalar] at h; omega)
      (by simp only [eventScalar] at h; omega)

def prependWork : Trace → Trace → ℕ
  | [],_ => 0
  | _::rest,suffix => prependWork rest suffix+(add (prepend rest suffix).2 4).2

theorem prepend_bound (events suffix : Trace) (Q : ℕ) (h : 4*events.length+8 ≤ Q) :
    prependWork events suffix ≤ 22*events.length*(binaryWordWidth Q+1) := by
  induction events with
  | nil => simp [prependWork]
  | cons event rest ih =>
    have hi := ih (by simp only [List.length_cons] at h; omega)
    have ha := add_bound (prepend rest suffix).2 4 Q
      (by rw [prepend_work]; simp only [List.length_cons] at h; omega) (by omega)
    simp only [prependWork,List.length_cons]
    nlinarith only [hi,ha]

def shiftedWork (depth : ℕ) : Trace → Trace → ℕ
  | [],_ => 0
  | event::rest,suffix =>
    let later := prependShifted depth rest suffix
    shiftedWork depth rest suffix+(add later.1.2 4).2+(add later.2 1).2+shiftWork depth event

theorem shifted_bound (depth : ℕ) (events suffix : Trace) (Q : ℕ)
    (h : 4*events.length+8 ≤ Q) (hScalar : depth+traceScalar events ≤ Q) :
    shiftedWork depth events suffix ≤ 66*events.length*(binaryWordWidth Q+1) := by
  induction events with
  | nil => simp [shiftedWork]
  | cons event rest ih =>
    have hi := ih (by simp only [List.length_cons] at h; omega)
      (by simp only [traceScalar] at hScalar; omega)
    have ha := add_bound (prependShifted depth rest suffix).1.2 4 Q
      (by rw [prependShifted_work]; simp only [List.length_cons] at h; omega) (by omega)
    have hb := add_bound (prependShifted depth rest suffix).2 1 Q
      (by rw [prependShifted_shifts]; simp only [List.length_cons] at h; omega) (by omega)
    have hs := shift_bound depth event Q (by simp only [traceScalar] at hScalar; omega)
    simp only [shiftedWork,List.length_cons]
    nlinarith only [hi,ha,hb,hs]

def emitWork : Plan → Trace → ℕ
  | .block events,suffix => prependWork events suffix
  | .shifted depth events,suffix => shiftedWork depth events suffix
  | .join first second,suffix =>
    let right := emitFull second suffix
    let left := emitFull first right.1.1
    emitWork second suffix+emitWork first right.1.1+
      (add left.1.2 right.1.2).2+(add (left.1.2+right.1.2) 2).2+(add left.2 right.2).2

theorem emit_bound (plan : Plan) (suffix : Trace) (Q : ℕ)
    (h : 4*payload plan+2*nodes plan+8 ≤ Q) (hScalar : planScalar plan ≤ Q) :
    emitWork plan suffix ≤ 66*(payload plan+nodes plan)*(binaryWordWidth Q+1) := by
  induction plan generalizing suffix with
  | block events =>
    have hp := prepend_bound events suffix Q (by simp only [payload,nodes] at h; omega)
    simp only [emitWork,payload,nodes]
    nlinarith only [hp]
  | shifted depth events =>
    have hs := shifted_bound depth events suffix Q (by simp only [payload,nodes] at h; omega) hScalar
    simp only [emitWork,payload,nodes]
    nlinarith only [hs]
  | join first second ihFirst ihSecond =>
    have hf := ihFirst (emitFull second suffix).1.1
      (by simp only [payload,nodes] at h; omega) (by simp only [planScalar] at hScalar; omega)
    have hs := ihSecond suffix (by simp only [payload,nodes] at h; omega)
      (by simp only [planScalar] at hScalar; omega)
    have hwf := emit_work first (emitFull second suffix).1.1
    have hws := emit_work second suffix
    rw [← emitFull_erases] at hwf hws
    have hcf := emitFull_shifts first (emitFull second suffix).1.1
    have hcs := emitFull_shifts second suffix
    have hbf := shiftCount_bound first
    have hbs := shiftCount_bound second
    have ha := add_bound (emitFull first (emitFull second suffix).1.1).1.2 (emitFull second suffix).1.2 Q
      (by simp only [payload,nodes] at h; omega) (by simp only [payload,nodes] at h; omega)
    have hb := add_bound ((emitFull first (emitFull second suffix).1.1).1.2+(emitFull second suffix).1.2) 2 Q
      (by simp only [payload,nodes] at h; omega) (by simp only [payload,nodes] at h; omega)
    have hc := add_bound (emitFull first (emitFull second suffix).1.1).2 (emitFull second suffix).2 Q
      (by simp only [payload,nodes] at h; omega) (by simp only [payload,nodes] at h; omega)
    simp only [emitWork,payload,nodes]
    nlinarith only [hf,hs,ha,hb,hc]

theorem emit_closed (plan : Plan) (suffix : Trace) :
    emitWork plan suffix ≤ 66*(payload plan+nodes plan)*
      (binaryWordWidth (4*payload plan+2*nodes plan+planScalar plan+8)+1) :=
  emit_bound plan suffix _ (by omega) (by omega)

theorem emit_width (plan : Plan) (suffix : Trace) :
    binaryWordWidth (emitWork plan suffix) ≤ binaryWordWidth (66*(payload plan+nodes plan)*
      (binaryWordWidth (4*payload plan+2*nodes plan+planScalar plan+8)+1)) :=
  binaryWordWidth_mono (emit_closed plan suffix)

def finishWork (plan : Plan) (suffix : Trace) : ℕ :=
  let emitted := emitFull plan suffix
  emitWork plan suffix+(add emitted.1.2 emitted.2).2

theorem finish_bound (plan : Plan) (suffix : Trace) (Q : ℕ)
    (h : 4*payload plan+2*nodes plan+8 ≤ Q) (hScalar : planScalar plan ≤ Q) :
    finishWork plan suffix ≤ 88*(payload plan+nodes plan+1)*(binaryWordWidth Q+1) := by
  have he := emit_bound plan suffix Q h hScalar
  have hw := emit_work plan suffix
  rw [← emitFull_erases] at hw
  have hs := emitFull_shifts plan suffix
  have hc := shiftCount_bound plan
  have ha := add_bound (emitFull plan suffix).1.2 (emitFull plan suffix).2 Q (by omega) (by omega)
  simp only [finishWork]
  nlinarith only [he,ha]

theorem finish_closed (plan : Plan) (suffix : Trace) :
    finishWork plan suffix ≤ 88*(payload plan+nodes plan+1)*
      (binaryWordWidth (4*payload plan+2*nodes plan+planScalar plan+8)+1) :=
  finish_bound plan suffix _ (by omega) (by omega)

end Blotto.BinaryTraceScalarWork
