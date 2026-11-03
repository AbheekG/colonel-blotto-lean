import Blotto.BinaryRulerControlMeasured

/-! Actual measured alignment, comparison and ruler selection feed their
returned values directly to their callers. Only the final selected ruler is
counted to form scalar precision. Old producers are erased proof references;
native observer/reservation arithmetic is outside this source model. -/
namespace Blotto.BinaryRulerPrecisionMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def shifted (word : PositiveBinaryWord) (ruler : List Bool) : (PositiveBinaryWord × Trace) × ℕ :=
  let zeros := BinaryRulerControlMeasured.falseMap ruler
  let appended := BinaryWordCoinPrimitivesMeasured.append word.tail zeros.1.1
  ((⟨appended.1.1⟩,wrap 24 2 [zeros.1.2,appended.1.2]),zeros.2+appended.2+4)

theorem shifted_erases (word : PositiveBinaryWord) (ruler : List Bool) :
    (shifted word ruler).1 = BinaryRulerPrecisionLifetime.shiftedWithTrace word ruler := by
  simp only [shifted,BinaryRulerPrecisionLifetime.shiftedWithTrace,
    BinaryRulerControlMeasured.falseMap_erases,BinaryWordCoinPrimitivesMeasured.append_erases]

theorem shifted_width (word : PositiveBinaryWord) (ruler : List Bool) :
    (shifted word ruler).1.1.width = word.width+ruler.length := by
  rw [shifted_erases,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,
    PositiveBinaryWord.width_shifted]

theorem shifted_work (word : PositiveBinaryWord) (ruler : List Bool) :
    (shifted word ruler).2 ≤ 4*(word.width+ruler.length+2) := by
  simp only [shifted,BinaryRulerControlMeasured.falseMap_work,BinaryWordCoinPrimitivesMeasured.append_work]
  unfold PositiveBinaryWord.width
  omega

def le (a b : PositiveBinaryWord) : (Bool × Trace) × ℕ :=
  let compared := BinaryRulerControlMeasured.compareLength a.tail b.tail
  match compared.1.1 with
  | .lt => ((true,wrap 16 2 [compared.1.2]),compared.2+4)
  | .gt => ((false,wrap 16 2 [compared.1.2]),compared.2+4)
  | .eq =>
      let scanned := BinaryRulerControlMeasured.leScan a.bits b.bits
      ((scanned.1.1,wrapList 2 24 2 [compared.1.2,scanned.1.2]),compared.2+scanned.2+4)

theorem le_erases (a b : PositiveBinaryWord) : (le a b).1 = BinaryRulerPrecisionLifetime.leWithTrace a b := by
  unfold le BinaryRulerPrecisionLifetime.leWithTrace
  dsimp only
  simp only [BinaryRulerControlMeasured.compareLength_erases,BinaryRulerControlMeasured.leScan_erases]
  cases (BinaryRulerControlLifetime.compareLengthWithTrace a.tail b.tail).1 <;> rfl

theorem le_work (a b : PositiveBinaryWord) : (le a b).2 ≤ 9*(a.width+1) := by
  have hc := BinaryRulerControlMeasured.compareLength_work a.tail b.tail
  have hs : (BinaryRulerControlMeasured.leScan a.bits b.bits).2 ≤ 5*a.width+2 := by
    simpa only [PositiveBinaryWord.bits,PositiveBinaryWord.width,List.length_cons] using
      BinaryRulerControlMeasured.leScan_work a.bits b.bits
  unfold le
  dsimp only
  split <;> unfold PositiveBinaryWord.width at * <;> omega

def prepare (a b : PositiveBinaryWord) : (List Bool × Trace) × ℕ :=
  let candidate := BinaryRulerControlMeasured.difference a.tail b.tail
  let aligned := shifted b candidate.1.1
  let compared := le a aligned.1.1
  let ruler := if compared.1.1 then candidate.1.1 else true::candidate.1.1
  ((ruler,wrapList 1 32 2 [candidate.1.2,aligned.1.2,compared.1.2]),candidate.2+aligned.2+compared.2+8)

theorem prepare_erases (a b : PositiveBinaryWord) :
    (prepare a b).1 = BinaryRulerPrecisionLifetime.prepareWithTrace a b := by
  simp only [prepare,BinaryRulerPrecisionLifetime.prepareWithTrace,
    BinaryRulerControlMeasured.difference_erases,shifted_erases,le_erases]

theorem prepare_length (a b : PositiveBinaryWord) : (prepare a b).1.1.length ≤ a.width := by
  rw [prepare_erases,BinaryRulerPrecisionLifetime.prepareWithTrace_state]
  exact BinaryRulerPrecision.prepare_length_bound a b

theorem prepare_work (a b : PositiveBinaryWord) : (prepare a b).2 ≤ 64*(a.width+b.width+1) := by
  have hd := BinaryRulerControlMeasured.difference_work a.tail b.tail
  have hCandidate : (BinaryRulerControlMeasured.difference a.tail b.tail).1.1.length ≤ a.tail.length := by
    rw [BinaryRulerControlMeasured.difference_erases,
      BinaryRulerControlLifetime.differenceWithTrace_state,BinaryRulerPrecision.difference_length]
    exact Nat.sub_le _ _
  have hShift := shifted_work b (BinaryRulerControlMeasured.difference a.tail b.tail).1.1
  have hWidth := shifted_width b (BinaryRulerControlMeasured.difference a.tail b.tail).1.1
  have hLe := le_work a (shifted b (BinaryRulerControlMeasured.difference a.tail b.tail).1.1).1.1
  unfold prepare
  dsimp only
  unfold PositiveBinaryWord.width at *
  omega

def length : List Bool → ℕ × ℕ
  | [] => (0,2)
  | _::rest => let later := length rest; (later.1+1,later.2+4)

theorem length_data (bits : List Bool) : (length bits).1 = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [length,List.length_cons,ih]

theorem length_work (bits : List Bool) : (length bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [length,List.length_cons,ih]; omega

def precision (a b : PositiveBinaryWord) : (ℕ × Trace) × ℕ :=
  let prepared := prepare a b
  let size := length prepared.1.1
  ((size.1,wrap 16 (size.1+2) [prepared.1.2]),prepared.2+size.2+4)

theorem precision_erases (a b : PositiveBinaryWord) :
    (precision a b).1 = BinaryRulerPrecisionLifetime.precisionWithTrace a b := by
  simp only [precision,BinaryRulerPrecisionLifetime.precisionWithTrace,length_data,prepare_erases]

theorem precision_work (a b : PositiveBinaryWord) : (precision a b).2 ≤ 128*(a.width+b.width+1) := by
  have hp := prepare_work a b
  have hl := prepare_length a b
  simp only [precision,length_work]
  omega

theorem precision_usage (a b : PositiveBinaryWord) : usage (precision a b).1.2 ≤ 512*(a.width+b.width+1) := by
  rw [precision_erases]
  exact BinaryRulerPrecisionLifetime.precisionWithTrace_usage a b

theorem all_prefix (a b : PositiveBinaryWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (precision a b).1.2 steps ≤ borrowed+512*(a.width+b.width+1) ∧
    framePeak ((precision a b).1.2.take steps) ≤ 512*(a.width+b.width+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (precision_usage a b) _ steps

end Blotto.BinaryRulerPrecisionMeasured
