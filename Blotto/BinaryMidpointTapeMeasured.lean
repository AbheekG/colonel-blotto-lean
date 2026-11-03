import Blotto.BinarySeedCursorMeasured

/-! The actual reverse/scan/reverse numerator and tape-recursive denominator
return the preceding midpoint word/trace and exact preceding source work.
Observer/reference/allocator evaluation remains outside this source contract. -/

namespace Blotto.BinaryMidpointTapeMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def drop : List Bool → (List Bool × Trace) × ℕ
  | [] => (([],[.frames 1]),2)
  | bits@(true::_) => ((bits,[.frames 1]),2)
  | false::rest =>
      let later := drop rest
      ((later.1.1,[.frames 1]++under 1 later.1.2),later.2+4)

theorem drop_erases (bits : List Bool) : (drop bits).1 = BinaryMidpointTapeLifetime.dropWithTrace bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [drop,BinaryMidpointTapeLifetime.dropWithTrace,ih]

theorem drop_work (bits : List Bool) : (drop bits).2 = (BinaryMidpointTapeLifetime.dropWithWork bits).2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [drop,BinaryMidpointTapeLifetime.dropWithWork,ih]

def trim (bits : List Bool) : (List Bool × Trace) × ℕ :=
  let front := BinarySeedCursorMeasured.reverse bits []
  let dropped := drop front.1.1
  let back := BinarySeedCursorMeasured.reverse dropped.1.1 []
  ((back.1.1,[.frames 2,.arrayAllocation 8]++under 2 front.1.2++under 2 dropped.1.2++under 2 back.1.2),
    front.2+dropped.2+back.2+8)

theorem trim_erases (bits : List Bool) : (trim bits).1 = BinaryMidpointTapeLifetime.trimWithTrace bits := by
  simp only [trim,BinaryMidpointTapeLifetime.trimWithTrace,BinarySeedCursorMeasured.reverse_erases,drop_erases]

theorem trim_work (bits : List Bool) : (trim bits).2 = (BinaryMidpointTapeLifetime.trimWithWork bits).2 := by
  simp only [trim,BinaryMidpointTapeLifetime.trimWithWork,BinarySeedCursorMeasured.reverse_work,drop_work,
    BinarySeedCursorMeasured.reverse_erases,← BinaryMidpointTapeLifetime.trim_work_state,
    BinaryMidpointTapeLifetime.reverse_work_state,reverseWithTrace_result,
    BinaryMidpointTapeLifetime.drop_work_state,drop_erases]

def denominator : List Bool → (List Bool × Trace) × ℕ
  | [] => (([true],[.frames 1,.listAllocation 1]),2)
  | _::rest =>
      let later := denominator rest
      ((false::later.1.1,[.frames 1,.listAllocation 1]++under 1 later.1.2),later.2+4)

theorem denominator_erases (seed : List Bool) :
    (denominator seed).1 = BinaryMidpointTapeLifetime.denominatorWithTrace seed := by
  induction seed with
  | nil => rfl
  | cons bit rest ih => simp only [denominator,BinaryMidpointTapeLifetime.denominatorWithTrace,ih]

theorem denominator_work (seed : List Bool) :
    (denominator seed).2 = (BinaryMidpointTapeLifetime.denominatorWithWork seed).2 := by
  induction seed with
  | nil => rfl
  | cons bit rest ih => simp only [denominator,BinaryMidpointTapeLifetime.denominatorWithWork,ih]

def sample (seed : List Bool) : (SignedWord × Trace) × ℕ :=
  let numerator := trim (true::seed)
  let denominator := denominator seed
  ((⟨false,numerator.1.1,false::denominator.1.1⟩,[.frames 2,.arrayAllocation 8,.listAllocation 2]++
    under 2 numerator.1.2++under 2 denominator.1.2),numerator.2+denominator.2+8)

theorem sample_erases (seed : List Bool) : (sample seed).1 = BinaryMidpointTapeLifetime.sampleWithTrace seed := by
  simp only [sample,BinaryMidpointTapeLifetime.sampleWithTrace,trim_erases,denominator_erases]

theorem sample_work (seed : List Bool) : (sample seed).2 = (BinaryMidpointTapeLifetime.sampleWithWork seed).2 := by
  simp only [sample,BinaryMidpointTapeLifetime.sampleWithWork,trim_work,denominator_work]

theorem sample_bound (seed : List Bool) : (sample seed).2 ≤ 20*(seed.length+2) := by
  rw [sample_work]
  exact BinaryMidpointTapeLifetime.sample_work seed

theorem all_prefix (seed : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (sample seed).1.2 steps ≤ borrowed+21*seed.length+58 ∧
      framePeak ((sample seed).1.2.take steps) ≤ 21*seed.length+58 := by
  rw [sample_erases]
  exact BinaryMidpointTapeLifetime.all_prefix seed borrowed steps

end Blotto.BinaryMidpointTapeMeasured
