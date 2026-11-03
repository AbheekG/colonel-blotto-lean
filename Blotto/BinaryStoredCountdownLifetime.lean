import Blotto.BinaryStoredCountdown
import Blotto.BinaryUnaryPayloadLifetime

/-! Actual little-endian borrow propagation copies only the reached prefix
and shares the untouched suffix. High zero padding is retained. All copied
cells/activations have reservations; no numeric dimension is decoded. -/
namespace Blotto.BinaryStoredCountdownLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def predecessorWithTrace : List Bool → List Bool × Trace
  | [] => ([],wrap 8 1 [])
  | true::rest => (false::rest,wrapList 1 8 1 [])
  | false::rest =>
      let later := predecessorWithTrace rest
      (true::later.1,wrapList 1 8 1 [later.2])

theorem predecessorWithTrace_state (counter : List Bool) :
    (predecessorWithTrace counter).1 = BinaryStoredCountdown.predecessor counter := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [predecessorWithTrace,BinaryStoredCountdown.predecessor,ih]

theorem predecessorWithTrace_length (counter : List Bool) : (predecessorWithTrace counter).1.length = counter.length := by
  rw [predecessorWithTrace_state,BinaryStoredCountdown.predecessor_length]

theorem predecessorWithTrace_value (counter : List Bool) (h : 0 < BinaryBigEndian.littleValue counter) :
    BinaryBigEndian.littleValue (predecessorWithTrace counter).1+1 = BinaryBigEndian.littleValue counter := by
  rw [predecessorWithTrace_state]
  exact BinaryStoredCountdown.predecessor_value counter h

theorem predecessorWithTrace_usage (counter : List Bool) : usage (predecessorWithTrace counter).2 ≤ 16*(counter.length+1) := by
  induction counter with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih =>
      cases bit
      · have h := wrapList_usage 1 8 1 [(predecessorWithTrace rest).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
        change usage (wrapList 1 8 1 [(predecessorWithTrace rest).2]) ≤ _
        simp only [List.length_cons]
        omega
      · exact (wrapList_usage 1 8 1 []).trans (by simp <;> omega)

theorem all_prefix (counter : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+counter.length) (predecessorWithTrace counter).2 steps ≤
      borrowed+counter.length+16*(counter.length+1) ∧
    framePeak ((predecessorWithTrace counter).2.take steps) ≤ 16*(counter.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (predecessorWithTrace_usage counter) _ steps

end Blotto.BinaryStoredCountdownLifetime
