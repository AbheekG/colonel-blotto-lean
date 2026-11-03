import Blotto.BinaryAccuracyMeasured
import Blotto.BinaryPRGRequestRulers

/-! Measured request assembly consumes retained parsed rows, actual Boolean
precision selection and structural triple loops. Full old request/trace
identity is preserved. Constant ruler construction, including a conservative
3000-cell overhead initialisation allowance, is included in source work.
Native reference-bit transport and observer/allocator arithmetic remain open. -/
namespace Blotto.BinaryPRGRequestRulersMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option autoImplicit false

def triple {α : Type*} : List α → List Bool → (List Bool × Trace) × ℕ
  | [],tail => ((tail,[.frames 1]),2)
  | _::rest,tail =>
      let later := triple rest tail
      ((false::false::false::later.1.1,[.frames 1,.listAllocation 3]++under 1 later.1.2),later.2+8)

theorem triple_erases {α : Type*} (items : List α) (tail : List Bool) :
    (triple items tail).1 = BinaryPRGRequestRulers.tripleWithTrace items tail := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [triple,BinaryPRGRequestRulers.tripleWithTrace,ih]

theorem triple_work {α : Type*} (items : List α) (tail : List Bool) :
    (triple items tail).2 = 8*items.length+2 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [triple,ih,List.length_cons]; omega

def choice {α : Type*} (rows : List α) (ruler : List Bool) : (List Bool × Trace) × ℕ :=
  let precision := triple ruler BinaryPRGRequestRulers.overhead
  let fields := triple rows precision.1.1
  ((fields.1.1,wrapList 3000 32 2 [precision.1.2,fields.1.2]),precision.2+fields.2+12004)

theorem choice_erases {α : Type*} (rows : List α) (ruler : List Bool) :
    (choice rows ruler).1 = BinaryPRGRequestRulers.choiceWithTrace rows ruler := by
  simp only [choice,BinaryPRGRequestRulers.choiceWithTrace,triple_erases]

theorem choice_work {α : Type*} (rows : List α) (ruler : List Bool) :
    (choice rows ruler).2 = 8*(rows.length+ruler.length)+12008 := by
  simp only [choice,triple_work]
  omega

def precision (accuracy : BinaryAccuracyRulerReadWork.Prepared) : (List Bool × Trace) × ℕ :=
  let shifted := BinaryRulerPrecisionMeasured.shifted accuracy.words.denominator (List.replicate 5 false)
  let selected := BinaryRulerPrecisionMeasured.prepare shifted.1.1 accuracy.words.numerator
  let zeros := BinaryRulerControlMeasured.falseMap selected.1.1
  ((zeros.1.1,wrapList 5 64 2 [shifted.1.2,selected.1.2,zeros.1.2]),shifted.2+selected.2+zeros.2+32)

theorem precision_erases (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precision accuracy).1 = BinaryPRGRequestRulers.precisionWithTrace accuracy := by
  simp only [precision,BinaryPRGRequestRulers.precisionWithTrace,
    BinaryRulerPrecisionMeasured.shifted_erases,BinaryRulerPrecisionMeasured.prepare_erases,
    BinaryRulerControlMeasured.falseMap_erases]

theorem precision_state (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precision accuracy).1.1 = List.replicate accuracy.precision false := by
  rw [precision_erases]
  exact BinaryPRGRequestRulers.precision_state accuracy

theorem precision_work (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (precision accuracy).2 ≤ 512*(accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  let shifted := BinaryRulerPrecisionMeasured.shifted accuracy.words.denominator (List.replicate 5 false)
  let selected := BinaryRulerPrecisionMeasured.prepare shifted.1.1 accuracy.words.numerator
  have hs := BinaryRulerPrecisionMeasured.shifted_work accuracy.words.denominator (List.replicate 5 false)
  have hp := BinaryRulerPrecisionMeasured.prepare_work shifted.1.1 accuracy.words.numerator
  have hz := BinaryRulerControlMeasured.falseMap_work selected.1.1
  have hWidth : shifted.1.1.width = accuracy.words.denominator.width+5 := by
    simpa only [shifted,List.length_replicate] using
      BinaryRulerPrecisionMeasured.shifted_width accuracy.words.denominator (List.replicate 5 false)
  have hLength : selected.1.1.length ≤ shifted.1.1.width :=
    BinaryRulerPrecisionMeasured.prepare_length shifted.1.1 accuracy.words.numerator
  simp only [List.length_replicate] at hs
  change shifted.2 ≤ _ at hs
  change selected.2 ≤ 64*(shifted.1.1.width+accuracy.words.numerator.width+1) at hp
  change shifted.2+selected.2+(BinaryRulerControlMeasured.falseMap selected.1.1).2+32 ≤ _
  omega

def assembleWithRows {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (BinaryPRGAccuracyRulerRequest.Request n × Trace) × ℕ :=
  let precision := precision accuracy
  let choice := choice rows precision.1.1
  have hP : precision.1.1 = List.replicate accuracy.precision false := precision_state accuracy
  have hC : choice.1.1 = List.replicate (coinBitBudget n accuracy.precision) false := by
    rw [choice_erases,BinaryPRGRequestRulers.choice_state,hP,hRows,List.length_replicate]
  ((⟨⟨checked.val,checked.property,accuracy.words,accuracy.precision,accuracy.correct⟩,header,
      precision.1.1,choice.1.1,hP,hC⟩,wrapList n 64 (n+4) [precision.1.2,choice.1.2]),precision.2+choice.2+8)

theorem assembleWithRows_erases {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (assembleWithRows checked accuracy header rows hRows).1 =
      BinaryPRGRequestRulers.assembleWithRows checked accuracy header rows hRows := by
  simp only [assembleWithRows,BinaryPRGRequestRulers.assembleWithRows,precision_erases,choice_erases]

theorem assembleWithRows_work {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (assembleWithRows checked accuracy header rows hRows).2 ≤
      1024*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) := by
  have hp := precision_work accuracy
  have hc := choice_work rows (precision accuracy).1.1
  have hPLength : (precision accuracy).1.1.length = accuracy.precision := by rw [precision_state,List.length_replicate]
  rw [hRows,hPLength] at hc
  have hK := accuracy.precision_bound
  change (precision accuracy).2+(choice rows (precision accuracy).1.1).2+8 ≤ _
  omega

theorem assembleWithRows_usage {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    usage (assembleWithRows checked accuracy header rows hRows).1.2 ≤
      10000*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) := by
  rw [assembleWithRows_erases]
  exact BinaryPRGRequestRulers.assembleWithRows_usage checked accuracy header rows hRows

theorem accepted_accuracy_joint {n : ℕ} (frame : List Bool)
    (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (hParsed : (BinaryAccuracyMeasured.read frame).1.1 = some parsed)
    (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n)
    (L : ℕ) (hL : frame.length ≤ L) (hn : n ≤ L) :
    (BinaryAccuracyMeasured.read frame).2+(assembleWithRows checked parsed.1 header rows hRows).2+
      usage (assembleWithRows checked parsed.1 header rows hRows).1.2 ≤ 50000*(L+1001) := by
  have hr := BinaryAccuracyMeasured.read_work frame
  have hWidths := BinaryAccuracyMeasured.read_widths frame parsed hParsed
  have hw := assembleWithRows_work checked parsed.1 header rows hRows
  have hu := assembleWithRows_usage checked parsed.1 header rows hRows
  unfold BinaryAccuracyMeasured.price at hr
  omega

theorem all_prefix {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) (borrowed steps : ℕ) :
    retainedHeap borrowed (assembleWithRows checked accuracy header rows hRows).1.2 steps ≤
      borrowed+10000*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) ∧
    framePeak ((assembleWithRows checked accuracy header rows hRows).1.2.take steps) ≤
      10000*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+1001) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (assembleWithRows_usage checked accuracy header rows hRows) _ steps

end Blotto.BinaryPRGRequestRulersMeasured
