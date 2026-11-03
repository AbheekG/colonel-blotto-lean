import Blotto.BinaryNumericalFinishScalarWork

/-! Some actual source boundaries accumulate an existing child emission charge
before the emitter's list/control and shift counters, using two left-associated
additions. Their Boolean scalar prices follow that exact association. -/
namespace Blotto.BinaryTraceScalarBaseWork
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceScalarWork
open BinaryTraceScalarReturnedBound (charge)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def work (plan : Plan) (suffix : Trace) (base : ℕ) : ℕ :=
  let emitted := emitFull plan suffix
  emitWork plan suffix+(add base emitted.1.2).2+(add (base+emitted.1.2) emitted.2).2

def total (plan : Plan) (suffix : Trace) (base : ℕ) : ℕ :=
  let emitted := emitFull plan suffix
  base+emitted.1.2+emitted.2

def ceiling (E U : ℕ) : ℕ := 110*E*(binaryWordWidth (E+U+8)+1)

theorem returned (plan : Plan) (suffix : Trace) (base : ℕ) :
    work plan suffix base ≤ ceiling (total plan suffix base) (framePeak (emitFull plan suffix).1.1) := by
  let E := total plan suffix base
  let F := framePeak (emitFull plan suffix).1.1
  let Q := E+F+8
  have hw := emit_work plan suffix
  rw [← emitFull_erases] at hw
  have hn := nodes_pos plan
  have hE : 4*payload plan+2*nodes plan ≤ E := by dsimp only [E,total]; omega
  have hF : framePeak (denote plan) ≤ F := by
    dsimp only [F]
    rw [emitFull_erases,emit_data,framePeak_append]
    exact Nat.le_max_left _ _
  have he := BinaryTraceScalarReturnedBound.emit_bound plan suffix Q
    (by dsimp only [Q]; omega) (by dsimp only [Q]; omega)
  have ha := add_bound base (emitFull plan suffix).1.2 Q
    (by dsimp only [Q,E,total]; omega) (by dsimp only [Q,E,total]; omega)
  have hb := add_bound (base+(emitFull plan suffix).1.2) (emitFull plan suffix).2 Q
    (by dsimp only [Q,E,total]; omega) (by dsimp only [Q,E,total]; omega)
  have hS : payload plan+nodes plan+1 ≤ E := by omega
  simp only [work,ceiling]
  dsimp only [E,F,Q] at he ha hb
  nlinarith only [he,ha,hb,hS]

theorem usage (plan : Plan) (suffix : Trace) (base : ℕ) :
    work plan suffix base ≤ ceiling (total plan suffix base)
      (BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1) := by
  have h := returned plan suffix base
  have hf : framePeak (emitFull plan suffix).1.1 ≤ BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1 := by
    unfold BinaryPRGHeapTraceUsage.usage
    omega
  have hw : binaryWordWidth (total plan suffix base+framePeak (emitFull plan suffix).1.1+8) ≤
      binaryWordWidth (total plan suffix base+BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1+8) :=
    binaryWordWidth_mono (by omega)
  unfold ceiling at *
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 1))

def allocations (plan : Plan) (suffix : Trace) (base : ℕ) : List ℕ :=
  let emitted := emitFull plan suffix
  BinaryTraceScalarAllocation.emit plan suffix++
    [(add base emitted.1.2).1.2,(add (base+emitted.1.2) emitted.2).1.2]

theorem allocations_sum (plan : Plan) (suffix : Trace) (base : ℕ) :
    (allocations plan suffix base).sum ≤ work plan suffix base := by
  have he := BinaryTraceScalarAllocation.emit_sum plan suffix
  have ha := add_allocated base (emitFull plan suffix).1.2
  have hb := add_allocated (base+(emitFull plan suffix).1.2) (emitFull plan suffix).2
  simp only [allocations,work,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

theorem all_prefix (plan : Plan) (suffix : Trace) (base borrowed steps : ℕ) :
    borrowed+((allocations plan suffix base).take steps).sum ≤ borrowed+ceiling (total plan suffix base)
      (BinaryPRGHeapTraceUsage.usage (emitFull plan suffix).1.1) := by
  have hp := BinaryTraceScalarAllocation.take_sum (allocations plan suffix base) steps
  have ha := allocations_sum plan suffix base
  have hw := usage plan suffix base
  omega

theorem polynomial (E U : ℕ) : ceiling E U ≤ 110*E*(E+U+10) := by
  have h := Nat.log2_le_self (E+U+8)
  unfold ceiling binaryWordWidth
  nlinarith only [h]

end Blotto.BinaryTraceScalarBaseWork
