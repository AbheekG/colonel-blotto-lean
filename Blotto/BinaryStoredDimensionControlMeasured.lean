import Blotto.BinaryStoredDimensionHeaderLifetime
import Blotto.BinaryStoredCountdownLifetime

/-! Explicit leading-zero and borrow loops retain the prior parser traces
and padding. Their work charges reached Boolean/list steps, independently
of the numerical value of an untrusted dimension. Visit fields are ghost
metadata; native observer arithmetic and allocator costs remain separate. -/
namespace Blotto.BinaryStoredDimensionControlMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def drop : List Bool → ((List Bool × ℕ) × Trace) × ℕ
  | [] => ((([],1),wrap 8 1 []),4)
  | true::rest => (((true::rest,1),wrapList 1 8 1 []),4)
  | false::rest =>
      let later := drop rest
      (((later.1.1.1,later.1.1.2+1),wrap 8 1 [later.1.2]),later.2+4)

theorem drop_erases (bits : List Bool) :
    (drop bits).1 = BinaryStoredDimensionHeaderLifetime.dropWithTrace bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [drop,BinaryStoredDimensionHeaderLifetime.dropWithTrace,ih]

theorem drop_work (bits : List Bool) : (drop bits).2 ≤ 4*(bits.length+1) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [drop,List.length_cons] <;> omega

theorem drop_length (bits : List Bool) : (drop bits).1.1.1.length ≤ bits.length := by
  rw [drop_erases,BinaryStoredDimensionHeaderLifetime.dropWithTrace_state]
  exact BinaryBigEndian.trim_length bits

theorem drop_usage (bits : List Bool) : usage (drop bits).1.2 ≤ 16*(bits.length+1) := by
  rw [drop_erases]
  exact BinaryStoredDimensionHeaderLifetime.dropWithTrace_usage bits

def predecessor : List Bool → (List Bool × Trace) × ℕ
  | [] => (([],wrap 8 1 []),4)
  | true::rest => ((false::rest,wrapList 1 8 1 []),4)
  | false::rest =>
      let later := predecessor rest
      ((true::later.1.1,wrapList 1 8 1 [later.1.2]),later.2+4)

theorem predecessor_erases (counter : List Bool) :
    (predecessor counter).1 = BinaryStoredCountdownLifetime.predecessorWithTrace counter := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [predecessor,BinaryStoredCountdownLifetime.predecessorWithTrace,ih]

theorem predecessor_work (counter : List Bool) :
    (predecessor counter).2 ≤ 4*(counter.length+1) := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [predecessor,List.length_cons] <;> omega

theorem predecessor_length (counter : List Bool) : (predecessor counter).1.1.length = counter.length := by
  rw [predecessor_erases]
  exact BinaryStoredCountdownLifetime.predecessorWithTrace_length counter

theorem predecessor_value (counter : List Bool) (h : 0 < BinaryBigEndian.littleValue counter) :
    BinaryBigEndian.littleValue (predecessor counter).1.1+1 = BinaryBigEndian.littleValue counter := by
  rw [predecessor_erases]
  exact BinaryStoredCountdownLifetime.predecessorWithTrace_value counter h

theorem predecessor_usage (counter : List Bool) : usage (predecessor counter).1.2 ≤ 16*(counter.length+1) := by
  rw [predecessor_erases]
  exact BinaryStoredCountdownLifetime.predecessorWithTrace_usage counter

theorem all_prefix (counter : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+counter.length) (predecessor counter).1.2 steps ≤
      borrowed+counter.length+16*(counter.length+1) ∧
    framePeak ((predecessor counter).1.2.take steps) ≤ 16*(counter.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (predecessor_usage counter) _ steps

end Blotto.BinaryStoredDimensionControlMeasured
