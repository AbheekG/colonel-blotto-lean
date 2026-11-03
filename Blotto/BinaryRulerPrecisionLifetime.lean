import Blotto.BinaryRulerControlLifetime

/-! Actual Boolean ruler alignment/selection. Returned cancellation suffixes,
false shifts and comparisons feed the selected ruler directly; only that
ruler's length becomes scalar precision. No old precision producer or numeric
accuracy-payload decoder is executed alongside the trace. -/
namespace Blotto.BinaryRulerPrecisionLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRulerControlLifetime

def shiftedWithTrace (word : PositiveBinaryWord) (ruler : List Bool) : PositiveBinaryWord × Trace :=
  let zeros := falseMapWithTrace ruler
  let appended := BinaryPRGOutputLifetime.appendWithTrace word.tail zeros.1
  (⟨appended.1⟩,wrap 24 2 [zeros.2,appended.2])

theorem shiftedWithTrace_state (word : PositiveBinaryWord) (ruler : List Bool) :
    (shiftedWithTrace word ruler).1 = BinaryRulerPrecision.shifted word ruler := by
  simp only [shiftedWithTrace,falseMapWithTrace_state,BinaryPRGOutputLifetime.appendWithTrace_state,BinaryRulerPrecision.shifted]

theorem shiftedWithTrace_usage (word : PositiveBinaryWord) (ruler : List Bool) :
    usage (shiftedWithTrace word ruler).2 ≤ 64*(word.width+ruler.length+1) := by
  have hZeros := falseMapWithTrace_usage ruler
  have hAppend := append_usage word.tail (falseMapWithTrace ruler).1
  have hw := wrap_usage 24 2 [(falseMapWithTrace ruler).2,
    (BinaryPRGOutputLifetime.appendWithTrace word.tail (falseMapWithTrace ruler).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (shiftedWithTrace word ruler).2 ≤ _ at hw
  unfold PositiveBinaryWord.width
  omega

def leWithTrace (a b : PositiveBinaryWord) : Bool × Trace :=
  let compared := compareLengthWithTrace a.tail b.tail
  match compared.1 with
  | .lt => (true,wrap 16 2 [compared.2])
  | .gt => (false,wrap 16 2 [compared.2])
  | .eq =>
      let scanned := leScanWithTrace a.bits b.bits
      (scanned.1,wrapList 2 24 2 [compared.2,scanned.2])

theorem leWithTrace_state (a b : PositiveBinaryWord) : (leWithTrace a b).1 = BinaryRulerPrecision.le a b := by
  unfold leWithTrace BinaryRulerPrecision.le
  dsimp only
  rw [compareLengthWithTrace_state]
  cases BinaryRulerPrecision.compareLength a.tail b.tail <;> simp only [leScanWithTrace_state]

theorem leWithTrace_usage (a b : PositiveBinaryWord) : usage (leWithTrace a b).2 ≤ 64*(a.width+1) := by
  have hCompare := compareLengthWithTrace_usage a.tail b.tail
  have hScan := leScanWithTrace_usage a.bits b.bits
  change usage (leScanWithTrace a.bits b.bits).2 ≤ 16*(a.width+1) at hScan
  unfold leWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(compareLengthWithTrace a.tail b.tail).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(compareLengthWithTrace a.tail b.tail).2]) ≤ _
    unfold PositiveBinaryWord.width
    omega
  · have hw := wrap_usage 16 2 [(compareLengthWithTrace a.tail b.tail).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(compareLengthWithTrace a.tail b.tail).2]) ≤ _
    unfold PositiveBinaryWord.width
    omega
  · have hw := wrapList_usage 2 24 2 [(compareLengthWithTrace a.tail b.tail).2,(leScanWithTrace a.bits b.bits).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrapList 2 24 2 [(compareLengthWithTrace a.tail b.tail).2,(leScanWithTrace a.bits b.bits).2]) ≤ _
    unfold PositiveBinaryWord.width at hScan ⊢
    omega

def prepareWithTrace (a b : PositiveBinaryWord) : List Bool × Trace :=
  let candidate := differenceWithTrace a.tail b.tail
  let aligned := shiftedWithTrace b candidate.1
  let compared := leWithTrace a aligned.1
  let ruler := if compared.1 then candidate.1 else true::candidate.1
  (ruler,wrapList 1 32 2 [candidate.2,aligned.2,compared.2])

theorem prepareWithTrace_state (a b : PositiveBinaryWord) :
    (prepareWithTrace a b).1 = (BinaryRulerPrecision.prepare a b).1 := by
  simp only [prepareWithTrace,BinaryRulerPrecision.prepare,differenceWithTrace_state,
    shiftedWithTrace_state,leWithTrace_state,BinaryRulerPrecision.leWithWork_state]

theorem prepareWithTrace_usage (a b : PositiveBinaryWord) : usage (prepareWithTrace a b).2 ≤ 256*(a.width+b.width+1) := by
  let candidate := differenceWithTrace a.tail b.tail
  let aligned := shiftedWithTrace b candidate.1
  have hDifference := differenceWithTrace_usage a.tail b.tail
  have hLength : candidate.1.length ≤ a.tail.length := by
    dsimp only [candidate]
    rw [differenceWithTrace_state,BinaryRulerPrecision.difference_length]
    exact Nat.sub_le _ _
  have hShift := shiftedWithTrace_usage b candidate.1
  have hCompare := leWithTrace_usage a aligned.1
  have hw := wrapList_usage 1 32 2 [candidate.2,aligned.2,(leWithTrace a aligned.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (prepareWithTrace a b).2 ≤ _ at hw
  change usage candidate.2 ≤ _ at hDifference
  change usage aligned.2 ≤ _ at hShift
  unfold PositiveBinaryWord.width at *
  omega

def precisionWithTrace (a b : PositiveBinaryWord) : ℕ × Trace :=
  let prepared := prepareWithTrace a b
  (prepared.1.length,wrap 16 (prepared.1.length+2) [prepared.2])

theorem precisionWithTrace_state (a b : PositiveBinaryWord) : (precisionWithTrace a b).1 = a.ratioPrecision b := by
  simp only [precisionWithTrace,prepareWithTrace_state,BinaryRulerPrecision.prepare_length]

theorem precisionWithTrace_usage (a b : PositiveBinaryWord) :
    usage (precisionWithTrace a b).2 ≤ 512*(a.width+b.width+1) := by
  have hPrepare := prepareWithTrace_usage a b
  have hLength : (prepareWithTrace a b).1.length ≤ a.width := by
    rw [prepareWithTrace_state]
    exact BinaryRulerPrecision.prepare_length_bound a b
  have hw := wrap_usage 16 ((prepareWithTrace a b).1.length+2) [(prepareWithTrace a b).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (precisionWithTrace a b).2 ≤ _ at hw
  omega

end Blotto.BinaryRulerPrecisionLifetime
