import Blotto.BinaryRulerPrecisionLifetime
import Blotto.BooleanSampleCountLifetime
import Blotto.BinaryPRGAccuracyRulerRequest
import Blotto.BinaryArrayProjectionLifetime

/-! Request preparation constructs the two actual validation rulers. Numeric
replicate defaults belong to the legacy reference constructor. The actual
assemblers use Boolean accuracy operations and structural row/ruler loops;
its fixed 3000-cell overhead is resident constant data, reserved explicitly. -/
namespace Blotto.BinaryPRGRequestRulers
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 2000000

def overhead : List Bool := List.replicate 3000 false

def tripleWithTrace {α : Type*} : List α → List Bool → List Bool × Trace
  | [],tail => (tail,[.frames 1])
  | _::rest,tail =>
      let later := tripleWithTrace rest tail
      (false::false::false::later.1,[.frames 1,.listAllocation 3] ++ under 1 later.2)

theorem triple_state {α : Type*} (items : List α) (T : ℕ) :
    (tripleWithTrace items (List.replicate T false)).1 = List.replicate (3*items.length+T) false := by
  induction items with
  | nil => simp only [tripleWithTrace,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons item rest ih =>
    simp only [tripleWithTrace,ih,List.length_cons]
    rw [show 3*(rest.length+1)+T = (3*rest.length+T)+1+1+1 by omega,
      List.replicate_succ,List.replicate_succ,List.replicate_succ]

theorem triple_bounds {α : Type*} (items : List α) (tail : List Bool) :
    listCells (tripleWithTrace items tail).2 = 3*items.length ∧
    arraySlots (tripleWithTrace items tail).2 = 0 ∧
    framePeak (tripleWithTrace items tail).2 ≤ items.length+1 := by
  induction items with
  | nil => simp [tripleWithTrace,listCells,arraySlots,framePeak]
  | cons item rest ih =>
    have hf := framePeak_under 1 (tripleWithTrace rest tail).2
    simp only [tripleWithTrace,listCells_append,arraySlots_append,framePeak_append,
      listCells,arraySlots,framePeak,listCells_under,arraySlots_under,List.length_cons]
    exact ⟨by omega,by omega,by omega⟩

def tripleWithWork {α : Type*} : List α → List Bool → List Bool × ℕ
  | [],tail => (tail,2)
  | _::rest,tail =>
      let later := tripleWithWork rest tail
      (false::false::false::later.1,later.2+8)

theorem triple_work_state {α : Type*} (items : List α) (tail : List Bool) :
    (tripleWithWork items tail).1 = (tripleWithTrace items tail).1 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [tripleWithWork,tripleWithTrace,ih]

theorem triple_work {α : Type*} (items : List α) (tail : List Bool) :
    (tripleWithWork items tail).2 = 8*items.length+2 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [tripleWithWork,ih,List.length_cons]; omega


def choiceWithTrace {α : Type*} (rows : List α) (ruler : List Bool) : List Bool × Trace :=
  let precision := tripleWithTrace ruler overhead
  let fields := tripleWithTrace rows precision.1
  (fields.1,wrapList 3000 32 2 [precision.2,fields.2])

theorem choice_state {α : Type*} (rows : List α) (ruler : List Bool) :
    (choiceWithTrace rows ruler).1 = List.replicate (coinBitBudget rows.length ruler.length) false := by
  simp only [choiceWithTrace,overhead,triple_state]
  unfold coinBitBudget
  congr 1
  omega

theorem choice_usage {α : Type*} (rows : List α) (ruler : List Bool) :
    usage (choiceWithTrace rows ruler).2 ≤ 64*(rows.length+ruler.length+1001) := by
  have hP := triple_bounds ruler overhead
  have hF := triple_bounds rows (tripleWithTrace ruler overhead).1
  have hw := wrapList_usage 3000 32 2
    [(tripleWithTrace ruler overhead).2,(tripleWithTrace rows (tripleWithTrace ruler overhead).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (choiceWithTrace rows ruler).2 ≤ _ at hw
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hw ⊢
  omega

def choiceWithWork {α : Type*} (rows : List α) (ruler : List Bool) : List Bool × ℕ :=
  let precision := tripleWithWork ruler overhead
  let fields := tripleWithWork rows precision.1
  (fields.1,precision.2+fields.2+2)

theorem choice_work_state {α : Type*} (rows : List α) (ruler : List Bool) :
    (choiceWithWork rows ruler).1 = (choiceWithTrace rows ruler).1 := by
  simp only [choiceWithWork,choiceWithTrace,triple_work_state]

theorem choice_work {α : Type*} (rows : List α) (ruler : List Bool) :
    (choiceWithWork rows ruler).2 = 8*(rows.length+ruler.length)+6 := by
  simp only [choiceWithWork,triple_work]
  omega


def precisionWithTrace (accuracy : BinaryAccuracyRulerReadWork.Prepared) : List Bool × Trace :=
  let shifted := BinaryRulerPrecisionLifetime.shiftedWithTrace accuracy.words.denominator (List.replicate 5 false)
  let selected := BinaryRulerPrecisionLifetime.prepareWithTrace shifted.1 accuracy.words.numerator
  let zeros := BinaryRulerControlLifetime.falseMapWithTrace selected.1
  (zeros.1,wrapList 5 64 2 [shifted.2,selected.2,zeros.2])

theorem precision_state (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precisionWithTrace accuracy).1 = List.replicate accuracy.precision false := by
  simp only [precisionWithTrace,BinaryRulerControlLifetime.falseMapWithTrace_state,
    BinaryRulerPrecisionLifetime.prepareWithTrace_state,BinaryStoredNatHeader.falseMap_eq,
    BinaryRulerPrecision.prepare_length,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,
    BinaryRulerPrecision.shifted_state,List.length_replicate]
  rw [accuracy.correct]
  rfl

theorem precision_usage (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    usage (precisionWithTrace accuracy).2 ≤ 2048*(accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  let shifted := BinaryRulerPrecisionLifetime.shiftedWithTrace accuracy.words.denominator (List.replicate 5 false)
  let selected := BinaryRulerPrecisionLifetime.prepareWithTrace shifted.1 accuracy.words.numerator
  have hShift := BinaryRulerPrecisionLifetime.shiftedWithTrace_usage accuracy.words.denominator (List.replicate 5 false)
  have hSelected := BinaryRulerPrecisionLifetime.prepareWithTrace_usage shifted.1 accuracy.words.numerator
  have hZeros := BinaryRulerControlLifetime.falseMapWithTrace_usage selected.1
  have hWidth : shifted.1.width = accuracy.words.denominator.width+5 := by
    simp only [shifted,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,
      PositiveBinaryWord.width_shifted,List.length_replicate]
  have hLength : selected.1.length = accuracy.precision := by
    rw [show selected.1 = (BinaryRulerPrecision.prepare shifted.1 accuracy.words.numerator).1 from
      BinaryRulerPrecisionLifetime.prepareWithTrace_state _ _,BinaryRulerPrecision.prepare_length]
    simp only [shifted,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,List.length_replicate]
    exact accuracy.correct.symm
  rw [hWidth] at hSelected
  rw [hLength] at hZeros
  have hK := accuracy.precision_bound
  simp only [List.length_replicate] at hShift
  have hw := wrapList_usage 5 64 2 [shifted.2,selected.2,(BinaryRulerControlLifetime.falseMapWithTrace selected.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage shifted.2 ≤ _ at hShift
  change usage selected.2 ≤ _ at hSelected
  change usage (precisionWithTrace accuracy).2 ≤ _ at hw
  omega

def assembleWithTrace {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) :
    BinaryPRGAccuracyRulerRequest.Request n × Trace :=
  let precision := precisionWithTrace accuracy
  let rows := BinaryArrayProjectionLifetime.readWithTrace checked.val.original.values.data
  let choice := choiceWithTrace rows.1 precision.1
  have hP : precision.1 = List.replicate accuracy.precision false := precision_state accuracy
  have hC : choice.1 = List.replicate (coinBitBudget n accuracy.precision) false := by
    rw [choice_state,hP,BinaryArrayProjectionLifetime.read_state,
      Array.length_toList,checked.val.original.values.size,List.length_replicate]
  (⟨⟨checked.val,checked.property,accuracy.words,accuracy.precision,accuracy.correct⟩,header,
      precision.1,choice.1,hP,hC⟩,wrapList n 64 (n+4) [precision.2,rows.2,choice.2])

theorem assemble_state {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) :
    (assembleWithTrace checked accuracy header).1 = BinaryPRGAccuracyRulerRequest.assemble checked accuracy header := by
  apply BinaryPRGAccuracyRulerRequest.Request.ext <;> rfl

theorem assemble_usage {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) :
    usage (assembleWithTrace checked accuracy header).2 ≤
      10000*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) := by
  have hp := precision_usage accuracy
  have hr := BinaryArrayProjectionLifetime.read_usage checked.val.original.values.data
  have hc := choice_usage
    (BinaryArrayProjectionLifetime.readWithTrace checked.val.original.values.data).1
    (precisionWithTrace accuracy).1
  have hPLength : (precisionWithTrace accuracy).1.length = accuracy.precision := by rw [precision_state,List.length_replicate]
  have hRows : (BinaryArrayProjectionLifetime.readWithTrace checked.val.original.values.data).1.length = n := by
    rw [BinaryArrayProjectionLifetime.read_state,Array.length_toList,checked.val.original.values.size]
  rw [hRows,hPLength] at hc
  rw [checked.val.original.values.size] at hr
  have hK := accuracy.precision_bound
  have hw := wrapList_usage n 64 (n+4) [(precisionWithTrace accuracy).2,
    (BinaryArrayProjectionLifetime.readWithTrace checked.val.original.values.data).2,
    (choiceWithTrace (BinaryArrayProjectionLifetime.readWithTrace checked.val.original.values.data).1
      (precisionWithTrace accuracy).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (assembleWithTrace checked accuracy header).2 ≤ _ at hw
  omega

/- The reached raw reader retains the parser's original row list. Supplying it
here avoids projecting the packed native array back to a list. -/
def assembleWithRows {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    BinaryPRGAccuracyRulerRequest.Request n × Trace :=
  let precision := precisionWithTrace accuracy
  let choice := choiceWithTrace rows precision.1
  have hP : precision.1 = List.replicate accuracy.precision false := precision_state accuracy
  have hC : choice.1 = List.replicate (coinBitBudget n accuracy.precision) false := by
    rw [choice_state,hP,hRows,List.length_replicate]
  (⟨⟨checked.val,checked.property,accuracy.words,accuracy.precision,accuracy.correct⟩,header,
      precision.1,choice.1,hP,hC⟩,wrapList n 64 (n+4) [precision.2,choice.2])

theorem assembleWithRows_state {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (assembleWithRows checked accuracy header rows hRows).1 =
      BinaryPRGAccuracyRulerRequest.assemble checked accuracy header := by
  apply BinaryPRGAccuracyRulerRequest.Request.ext <;> rfl

theorem assembleWithRows_usage {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    usage (assembleWithRows checked accuracy header rows hRows).2 ≤
      10000*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) := by
  have hp := precision_usage accuracy
  have hc := choice_usage rows (precisionWithTrace accuracy).1
  have hPLength : (precisionWithTrace accuracy).1.length = accuracy.precision := by
    rw [precision_state,List.length_replicate]
  rw [hRows,hPLength] at hc
  have hK := accuracy.precision_bound
  have hw := wrapList_usage n 64 (n+4) [(precisionWithTrace accuracy).2,
    (choiceWithTrace rows (precisionWithTrace accuracy).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (assembleWithRows checked accuracy header rows hRows).2 ≤ _ at hw
  omega

end Blotto.BinaryPRGRequestRulers
