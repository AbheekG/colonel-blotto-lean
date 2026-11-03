import Blotto.BinaryPRGRequestRulers

/-! Measured Boolean/list counterpart of the actual precision-ruler path.
Every recursive producer returns the data consumed by its parent. Natural work
charges are ghost counters; the traced root remains the actual source path. -/
namespace Blotto.BinaryRulerPrecisionWork
open BinaryRulerControlLifetime BinaryRulerPrecisionLifetime
set_option maxHeartbeats 2000000

def differenceWithWork : List Bool → List Bool → List Bool × ℕ
  | bits, [] => (bits,2)
  | [], _::_ => ([],2)
  | _::bits, _::other =>
      let later := differenceWithWork bits other
      (later.1,later.2+4)

theorem difference_state (bits other : List Bool) :
    (differenceWithWork bits other).1 = (differenceWithTrace bits other).1 := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => exact ih tail

theorem difference_work (bits other : List Bool) :
    (differenceWithWork bits other).2 ≤ 4*(bits.length+1) := by
  induction bits generalizing other with
  | nil => cases other <;> simp [differenceWithWork]
  | cons bit rest ih => cases other with
    | nil => simp only [differenceWithWork,List.length_cons]; omega
    | cons head tail =>
        have ht := ih tail
        simp only [differenceWithWork,List.length_cons]
        omega

def compareLengthWithWork : List Bool → List Bool → Ordering × ℕ
  | [], [] => (.eq,2)
  | [], _::_ => (.lt,2)
  | _::_, [] => (.gt,2)
  | _::bits, _::other =>
      let later := compareLengthWithWork bits other
      (later.1,later.2+4)

theorem compareLength_state (bits other : List Bool) :
    (compareLengthWithWork bits other).1 = (compareLengthWithTrace bits other).1 := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => exact ih tail

theorem compareLength_work (bits other : List Bool) :
    (compareLengthWithWork bits other).2 ≤ 4*(bits.length+1) := by
  induction bits generalizing other with
  | nil => cases other <;> simp [compareLengthWithWork]
  | cons bit rest ih => cases other with
    | nil => simp only [compareLengthWithWork,List.length_cons]; omega
    | cons head tail =>
        have ht := ih tail
        simp only [compareLengthWithWork,List.length_cons]
        omega

def leScanWithWork : List Bool → List Bool → Bool × ℕ
  | [], _ => (true,2)
  | _::_, [] => (false,2)
  | a::bits, b::other =>
      if a = b then
        let later := leScanWithWork bits other
        (later.1,later.2+5)
      else (!a,5)

theorem leScan_state (bits other : List Bool) :
    (leScanWithWork bits other).1 = (leScanWithTrace bits other).1 := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail =>
        simp only [leScanWithWork,leScanWithTrace]
        split <;> simp only [ih]

theorem leScan_work (bits other : List Bool) :
    (leScanWithWork bits other).2 ≤ 5*bits.length+2 := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit rest ih => cases other with
    | nil => simp [leScanWithWork]
    | cons head tail =>
        have ht := ih tail
        unfold leScanWithWork
        split <;> simp only [List.length_cons] <;> omega

def falseMapWithWork : List Bool → List Bool × ℕ
  | [] => ([],2)
  | _::rest =>
      let later := falseMapWithWork rest
      (false::later.1,later.2+4)

theorem falseMap_state (bits : List Bool) :
    (falseMapWithWork bits).1 = (falseMapWithTrace bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMapWithWork,falseMapWithTrace,ih]

theorem falseMap_work (bits : List Bool) :
    (falseMapWithWork bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMapWithWork,ih,List.length_cons]; omega

def appendWithWork : List Bool → List Bool → List Bool × ℕ
  | [],right => (right,2)
  | bit::left,right =>
      let later := appendWithWork left right
      (bit::later.1,later.2+4)

theorem append_state (left right : List Bool) :
    (appendWithWork left right).1 = (BinaryPRGOutputLifetime.appendWithTrace left right).1 := by
  induction left with
  | nil => rfl
  | cons bit rest ih => simp only [appendWithWork,BinaryPRGOutputLifetime.appendWithTrace,ih]

theorem append_work (left right : List Bool) :
    (appendWithWork left right).2 = 4*left.length+2 := by
  induction left with
  | nil => rfl
  | cons bit rest ih => simp only [appendWithWork,ih,List.length_cons]; omega

def shiftedWithWork (word : PositiveBinaryWord) (ruler : List Bool) : PositiveBinaryWord × ℕ :=
  let zeros := falseMapWithWork ruler
  let appended := appendWithWork word.tail zeros.1
  (⟨appended.1⟩,zeros.2+appended.2+4)

theorem shifted_state (word : PositiveBinaryWord) (ruler : List Bool) :
    (shiftedWithWork word ruler).1 = (shiftedWithTrace word ruler).1 := by
  simp only [shiftedWithWork,shiftedWithTrace,falseMap_state,append_state]

theorem shifted_work (word : PositiveBinaryWord) (ruler : List Bool) :
    (shiftedWithWork word ruler).2 ≤ 4*(word.width+ruler.length+2) := by
  simp only [shiftedWithWork,falseMap_work,append_work]
  unfold PositiveBinaryWord.width
  omega

def leWithWork (a b : PositiveBinaryWord) : Bool × ℕ :=
  let compared := compareLengthWithWork a.tail b.tail
  match compared.1 with
  | .lt => (true,compared.2+4)
  | .gt => (false,compared.2+4)
  | .eq =>
      let scanned := leScanWithWork a.bits b.bits
      (scanned.1,compared.2+scanned.2+4)

theorem le_state (a b : PositiveBinaryWord) :
    (leWithWork a b).1 = (leWithTrace a b).1 := by
  unfold leWithWork leWithTrace
  dsimp only
  rw [compareLength_state]
  cases (compareLengthWithTrace a.tail b.tail).1 <;> simp only [leScan_state]

theorem le_work (a b : PositiveBinaryWord) :
    (leWithWork a b).2 ≤ 9*(a.width+1) := by
  have hc := compareLength_work a.tail b.tail
  have hs : (leScanWithWork a.bits b.bits).2 ≤ 5*a.width+2 := by
    simpa only [PositiveBinaryWord.bits,PositiveBinaryWord.width,List.length_cons] using
      leScan_work a.bits b.bits
  unfold leWithWork
  dsimp only
  split <;> unfold PositiveBinaryWord.width at * <;> omega

def prepareWithWork (a b : PositiveBinaryWord) : List Bool × ℕ :=
  let candidate := differenceWithWork a.tail b.tail
  let aligned := shiftedWithWork b candidate.1
  let compared := leWithWork a aligned.1
  let ruler := if compared.1 then candidate.1 else true::candidate.1
  (ruler,candidate.2+aligned.2+compared.2+5)

theorem prepare_state (a b : PositiveBinaryWord) :
    (prepareWithWork a b).1 = (prepareWithTrace a b).1 := by
  simp only [prepareWithWork,prepareWithTrace,difference_state,shifted_state,le_state]

theorem prepare_work (a b : PositiveBinaryWord) :
    (prepareWithWork a b).2 ≤ 32*(a.width+b.width+1) := by
  have hd := difference_work a.tail b.tail
  have hCandidate : (differenceWithWork a.tail b.tail).1.length ≤ a.tail.length := by
    rw [difference_state,differenceWithTrace_state,BinaryRulerPrecision.difference_length]
    exact Nat.sub_le _ _
  have hShift := shifted_work b (differenceWithWork a.tail b.tail).1
  have hLe := le_work a (shiftedWithWork b (differenceWithWork a.tail b.tail).1).1
  unfold prepareWithWork
  dsimp only
  unfold PositiveBinaryWord.width at *
  omega

def precisionWithWork (accuracy : BinaryAccuracyRulerReadWork.Prepared) : List Bool × ℕ :=
  let shifted := shiftedWithWork accuracy.words.denominator (List.replicate 5 false)
  let selected := prepareWithWork shifted.1 accuracy.words.numerator
  let zeros := falseMapWithWork selected.1
  (zeros.1,shifted.2+selected.2+zeros.2+5)

theorem precision_state (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precisionWithWork accuracy).1 = (BinaryPRGRequestRulers.precisionWithTrace accuracy).1 := by
  simp only [precisionWithWork,BinaryPRGRequestRulers.precisionWithTrace,
    shifted_state,prepare_state,falseMap_state]

theorem precision_work (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precisionWithWork accuracy).2 ≤
      256*(accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  let shifted := shiftedWithWork accuracy.words.denominator (List.replicate 5 false)
  let selected := prepareWithWork shifted.1 accuracy.words.numerator
  have hShift := shifted_work accuracy.words.denominator (List.replicate 5 false)
  have hSelected := prepare_work shifted.1 accuracy.words.numerator
  have hZeros := falseMap_work selected.1
  have hWidth : shifted.1.width = accuracy.words.denominator.width+5 := by
    simp only [shifted,shifted_state,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,
      BinaryRulerPrecision.shifted_state,PositiveBinaryWord.width_shifted,List.length_replicate]
  have hLength : selected.1.length = accuracy.precision := by
    rw [show selected.1 = (BinaryRulerPrecisionLifetime.prepareWithTrace shifted.1 accuracy.words.numerator).1 from
      prepare_state _ _,BinaryRulerPrecisionLifetime.prepareWithTrace_state,
      BinaryRulerPrecision.prepare_length]
    rw [show shifted.1 = BinaryRulerPrecision.shifted accuracy.words.denominator (List.replicate 5 false) from
      (shifted_state _ _).trans (BinaryRulerPrecisionLifetime.shiftedWithTrace_state _ _)]
    rw [BinaryRulerPrecision.shifted_state,List.length_replicate]
    exact accuracy.correct.symm
  have hK := accuracy.precision_bound
  simp only [List.length_replicate] at hShift
  rw [hWidth] at hSelected
  rw [hLength] at hZeros
  have hSelectedCost :
      (prepareWithWork (shiftedWithWork accuracy.words.denominator (List.replicate 5 false)).1
        accuracy.words.numerator).2 ≤
        32*(accuracy.words.denominator.width+5+accuracy.words.numerator.width+1) := by
    simpa only [shifted] using hSelected
  have hZerosCost :
      (falseMapWithWork
        (prepareWithWork (shiftedWithWork accuracy.words.denominator (List.replicate 5 false)).1
          accuracy.words.numerator).1).2 = 4*accuracy.precision+2 := by
    simpa only [shifted,selected] using hZeros
  unfold precisionWithWork
  dsimp only
  omega

def rulersWithWork {α : Type*} (rows : List α)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (List Bool × List Bool) × ℕ :=
  let precision := precisionWithWork accuracy
  let choice := BinaryPRGRequestRulers.choiceWithWork rows precision.1
  ((precision.1,choice.1),precision.2+choice.2+4)

theorem rulers_state {α : Type*} (rows : List α)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (rulersWithWork rows accuracy).1 =
      ((BinaryPRGRequestRulers.precisionWithTrace accuracy).1,
        (BinaryPRGRequestRulers.choiceWithTrace rows
          (BinaryPRGRequestRulers.precisionWithTrace accuracy).1).1) := by
  simp only [rulersWithWork,precision_state,BinaryPRGRequestRulers.choice_work_state]

theorem rulers_work {α : Type*} (rows : List α)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (rulersWithWork rows accuracy).2 ≤
      512*(rows.length+accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  have hp := precision_work accuracy
  have hc := BinaryPRGRequestRulers.choice_work rows (precisionWithWork accuracy).1
  have hLength : (precisionWithWork accuracy).1.length = accuracy.precision := by
    rw [precision_state,BinaryPRGRequestRulers.precision_state,List.length_replicate]
  have hK := accuracy.precision_bound
  rw [hLength] at hc
  unfold rulersWithWork
  dsimp only
  omega

end Blotto.BinaryRulerPrecisionWork
