import Blotto.BinaryHeapTapeMeasured
import Blotto.BinaryTapeFrameLifetime

/-! Boolean ruler, payload and signed-word framing return data, the selected
source trace and its work annotation from a single recursive producer. -/

namespace Blotto.BinaryTapeFrameMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000

def ruler : List Bool → (List Bool × Trace) × ℕ
  | [] => (([],wrap 8 1 []),2)
  | _::rest =>
      let later := ruler rest
      ((false::later.1.1,wrap 16 1 [later.1.2]),later.2+4)

theorem ruler_erases (bits : List Bool) :
    (ruler bits).1 = BinaryTapeFrameLifetime.rulerWithTrace bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [ruler,BinaryTapeFrameLifetime.rulerWithTrace,ih]

theorem ruler_data (bits : List Bool) :
    (ruler bits).1.1 = (BinaryTapeFrameLifetime.rulerWithWork bits).1 := by
  have h := congrArg Prod.fst (ruler_erases bits)
  exact h.trans (BinaryTapeFrameLifetime.ruler_state bits)

theorem ruler_work (bits : List Bool) :
    (ruler bits).2 = (BinaryTapeFrameLifetime.rulerWithWork bits).2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [ruler,BinaryTapeFrameLifetime.rulerWithWork,ih]

def payload (bits : List Bool) : (List Bool × Trace) × ℕ :=
  let counted := ruler bits
  let joined := BinaryHeapTapeMeasured.append counted.1.1 (true::bits)
  ((joined.1.1,wrap 32 2 [counted.1.2,joined.1.2]),counted.2+joined.2.work+4)

theorem payload_erases (bits : List Bool) :
    (payload bits).1 = BinaryTapeFrameLifetime.payloadWithTrace bits := by
  simp only [payload,BinaryTapeFrameLifetime.payloadWithTrace,ruler_erases,
    BinaryHeapTapeMeasured.append_erases]

theorem payload_data (bits : List Bool) :
    (payload bits).1.1 = (BinaryTapeFrameLifetime.payloadWithWork bits).1 := by
  have h := congrArg Prod.fst (payload_erases bits)
  exact h.trans (BinaryTapeFrameLifetime.payload_state bits)

theorem payload_work (bits : List Bool) :
    (payload bits).2 = (BinaryTapeFrameLifetime.payloadWithWork bits).2 := by
  simp only [payload,BinaryTapeFrameLifetime.payloadWithWork,ruler_work,ruler_data,
    BinaryHeapTapeMeasured.append_charge]

def word (value : SignedWord) : (List Bool × Trace) × ℕ :=
  let numerator := payload value.numerator
  let denominator := payload value.denominator
  let joined := BinaryHeapTapeMeasured.append numerator.1.1 denominator.1.1
  ((value.negative::joined.1.1,wrap 48 2 [numerator.1.2,denominator.1.2,joined.1.2]),
    numerator.2+denominator.2+joined.2.work+8)

theorem word_erases (value : SignedWord) :
    (word value).1 = BinaryTapeFrameLifetime.wordWithTrace value := by
  simp only [word,BinaryTapeFrameLifetime.wordWithTrace,payload_erases,
    BinaryHeapTapeMeasured.append_erases]

theorem word_data (value : SignedWord) :
    (word value).1.1 = (BinaryTapeFrameLifetime.wordWithWork value).1 := by
  have h := congrArg Prod.fst (word_erases value)
  exact h.trans (BinaryTapeFrameLifetime.word_state value)

theorem word_work (value : SignedWord) :
    (word value).2 = (BinaryTapeFrameLifetime.wordWithWork value).2 := by
  simp only [word,BinaryTapeFrameLifetime.wordWithWork,payload_work,payload_data,
    BinaryHeapTapeMeasured.append_charge]

theorem payload_bound (bits : List Bool) : (payload bits).2 ≤ 16*(bits.length+1) := by
  rw [payload_work]
  exact BinaryTapeFrameLifetime.payload_work bits

theorem word_bound (value : SignedWord) : (word value).2 ≤ 128*(width value+1) := by
  rw [word_work]
  exact BinaryTapeFrameLifetime.word_work value

theorem word_all_prefix (value : SignedWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (word value).1.2 steps ≤ borrowed+1024*(width value+1) ∧
      framePeak ((word value).1.2.take steps) ≤ 1024*(width value+1) := by
  rw [word_erases]
  exact all_prefix _ _ (BinaryTapeFrameLifetime.word_usage value) borrowed steps

end Blotto.BinaryTapeFrameMeasured
