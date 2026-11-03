import Blotto.BinaryTraceScalarAllocation

/-! Actual returned work and frame events bound the emitter's canonical
Boolean scalar additions. No separate input scalar-field ceiling is supplied.
Canonical operand formation and full native-model interpretation remain open. -/
namespace Blotto.BinaryTraceScalarReturnedBound
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceScalarWork
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem shift_tail (depth : ℕ) (event : Event) (rest : Trace) :
    framePeak (under depth rest) ≤ framePeak (under depth (event::rest)) := by
  cases event <;> simp [under,shiftEvent,framePeak]

theorem shift_head (depth : ℕ) (event : Event) (rest : Trace) (Q : ℕ)
    (h : framePeak (under depth (event::rest)) ≤ Q) :
    shiftWork depth event ≤ 22*(binaryWordWidth Q+1) := by
  cases event with
  | listAllocation n => exact Nat.zero_le _
  | arrayAllocation n => exact Nat.zero_le _
  | frames n =>
    simp only [under,List.map_cons,shiftEvent,framePeak] at h
    exact add_bound depth n Q (by omega) (by omega)

theorem shifted_bound (depth : ℕ) (events suffix : Trace) (Q : ℕ)
    (h : 4*events.length+8 ≤ Q) (hFrame : framePeak (under depth events) ≤ Q) :
    shiftedWork depth events suffix ≤ 66*events.length*(binaryWordWidth Q+1) := by
  induction events with
  | nil => simp [shiftedWork]
  | cons event rest ih =>
    have hi := ih (by simp only [List.length_cons] at h; omega)
      ((shift_tail depth event rest).trans hFrame)
    have ha := add_bound (prependShifted depth rest suffix).1.2 4 Q
      (by rw [prependShifted_work]; simp only [List.length_cons] at h; omega) (by omega)
    have hb := add_bound (prependShifted depth rest suffix).2 1 Q
      (by rw [prependShifted_shifts]; simp only [List.length_cons] at h; omega) (by omega)
    have hs := shift_head depth event rest Q hFrame
    simp only [shiftedWork,List.length_cons]
    nlinarith only [hi,ha,hb,hs]

theorem emit_bound (plan : Plan) (suffix : Trace) (Q : ℕ)
    (h : 4*payload plan+2*nodes plan+8 ≤ Q) (hFrame : framePeak (denote plan) ≤ Q) :
    emitWork plan suffix ≤ 66*(payload plan+nodes plan)*(binaryWordWidth Q+1) := by
  induction plan generalizing suffix with
  | block events =>
    have hp := prepend_bound events suffix Q (by simp only [payload,nodes] at h; omega)
    simp only [emitWork,payload,nodes]
    nlinarith only [hp]
  | shifted depth events =>
    have hs := shifted_bound depth events suffix Q (by simp only [payload,nodes] at h; omega) hFrame
    simp only [emitWork,payload,nodes]
    nlinarith only [hs]
  | join first second ihFirst ihSecond =>
    have hf := ihFirst (emitFull second suffix).1.1 (by simp only [payload,nodes] at h; omega)
      (by simp only [denote,framePeak_append] at hFrame; omega)
    have hs := ihSecond suffix (by simp only [payload,nodes] at h; omega)
      (by simp only [denote,framePeak_append] at hFrame; omega)
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

def charge (plan : Plan) (suffix : Trace) : ℕ := (emitFull plan suffix).1.2+(emitFull plan suffix).2

def ceiling (emission frames : ℕ) : ℕ := 88*emission*(binaryWordWidth (emission+frames+8)+1)

theorem ceiling_mono {E F U V : ℕ} (hE : E ≤ F) (hU : U ≤ V) : ceiling E U ≤ ceiling F V := by
  have hw := binaryWordWidth_mono (show E+U+8 ≤ F+V+8 by omega)
  unfold ceiling
  gcongr

theorem finish_returned (plan : Plan) (suffix : Trace) :
    finishWork plan suffix ≤ ceiling (charge plan suffix) (framePeak (emitFull plan suffix).1.1) := by
  let E := charge plan suffix
  let F := framePeak (emitFull plan suffix).1.1
  let Q := E+F+8
  have hw := emit_work plan suffix
  rw [← emitFull_erases] at hw
  have hs := emitFull_shifts plan suffix
  have hc := shiftCount_bound plan
  have hn := nodes_pos plan
  have hE : 4*payload plan+2*nodes plan ≤ E := by dsimp only [E,charge]; omega
  have hF : framePeak (denote plan) ≤ F := by
    dsimp only [F]
    rw [emitFull_erases,emit_data,framePeak_append]
    exact Nat.le_max_left _ _
  have he := emit_bound plan suffix Q (by dsimp only [Q]; omega) (by dsimp only [Q]; omega)
  have ha := add_bound (emitFull plan suffix).1.2 (emitFull plan suffix).2 Q
    (by dsimp only [Q,E,charge]; omega) (by dsimp only [Q,E,charge]; omega)
  have hS : payload plan+nodes plan+1 ≤ E := by omega
  simp only [finishWork,ceiling]
  dsimp only [E,F,Q] at he ha
  nlinarith only [he,ha,hS]

theorem finish_usage (plan : Plan) (suffix : Trace) :
    finishWork plan suffix ≤ ceiling (charge plan suffix)
      (BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1) := by
  have hf : framePeak (emitFull plan suffix).1.1 ≤ BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1 := by
    unfold BinaryPRGHeapTraceUsage.usage
    omega
  exact (finish_returned plan suffix).trans (ceiling_mono (Nat.le_refl _) hf)

theorem ceiling_polynomial (E U : ℕ) : ceiling E U ≤ 88*E*(E+U+10) := by
  have h := Nat.log2_le_self (E+U+8)
  unfold ceiling binaryWordWidth
  nlinarith only [h]

theorem all_prefix (plan : Plan) (suffix : Trace) (borrowed steps : ℕ) :
    borrowed+((BinaryTraceScalarAllocation.finish plan suffix).take steps).sum ≤
      borrowed+ceiling (charge plan suffix) (BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1) := by
  have hp := BinaryTraceScalarAllocation.take_sum (BinaryTraceScalarAllocation.finish plan suffix) steps
  have ha := BinaryTraceScalarAllocation.finish_sum plan suffix
  have hw := finish_usage plan suffix
  omega

end Blotto.BinaryTraceScalarReturnedBound
