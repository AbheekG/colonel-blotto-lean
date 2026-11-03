import Blotto.GeneralPaperMeasuredBitDispatch

/-! Repricing initialization at a larger reference preserves its actual
data and only increases its executed work. These inequalities compare one
run's prices; no second preparation is executed. -/
namespace Blotto.GeneralPaperMeasuredInitializerMonotonicity
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem count (A B : ℕ) (h : A ≤ B) (bits : List Bool) :
    (GeneralPaperBinaryAccuracy.count id A bits).2 ≤ (GeneralPaperBinaryAccuracy.count id B bits).2 := by
  induction bits with
  | nil => simp only [GeneralPaperBinaryAccuracy.count]; omega
  | cons bit rest ih =>
    simp only [GeneralPaperBinaryAccuracy.count, GeneralPaperBinaryAccuracy.count_data]
    omega

theorem accuracy (A B : ℕ) (h : A ≤ B) (words : BinaryAccuracyWords) :
    (GeneralPaperBinaryAccuracy.prepare id A words).2 ≤ (GeneralPaperBinaryAccuracy.prepare id B words).2 := by
  let ruler := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  have hc := count A B h ruler.1
  have hr := Nat.mul_le_mul_left ruler.2 h
  dsimp only [GeneralPaperBinaryAccuracy.prepare]
  dsimp only [ruler] at hc hr
  omega

theorem scalar (model : RationalCostModel) (A B : ℕ) (h : A ≤ B)
    (op : GeneralPaperNaturalScalarStep.Op) (a b : ℕ) :
    (GeneralPaperNaturalScalarStep.run model A op a b).2 ≤
      (GeneralPaperNaturalScalarStep.run model B op a b).2 := by
  dsimp only [GeneralPaperNaturalScalarStep.run]
  omega

theorem rational (model : RationalCostModel) (A B : ℕ) (h : A ≤ B) (q : ℚ) :
    (GeneralPaperStoredRationalWordLength.run model A q).2 ≤
      (GeneralPaperStoredRationalWordLength.run model B q).2 := by
  dsimp only [GeneralPaperStoredRationalWordLength.run, GeneralPaperStoredWordLength.run,
    GeneralPaperNaturalScalarStep.run, GeneralPaperNaturalScalarStep.Op.apply]
  omega

theorem value_scan {n : ℕ} (model : RationalCostModel) (A B : ℕ) (h : A ≤ B)
    (values : FixedArrayTable n ℚ) (items : List (Fin n)) :
    (GeneralPaperValueInputWordLength.scan model A values items).2 ≤
      (GeneralPaperValueInputWordLength.scan model B values items).2 := by
  induction items with
  | nil => simp only [GeneralPaperValueInputWordLength.scan]; omega
  | cons j rest ih =>
    have hr := rational model A B h (values.read j)
    have hs := scalar model A B h .add (rationalWordWidth (values.read j))
      (GeneralPaperValueInputWordLength.size values rest)
    have hu : GeneralPaperEqualPackingExecution.unit A n ≤ GeneralPaperEqualPackingExecution.unit B n := by
      unfold GeneralPaperEqualPackingExecution.unit
      omega
    simp only [GeneralPaperValueInputWordLength.scan, GeneralPaperValueInputWordLength.scan_data,
      GeneralPaperStoredRationalWordLength.data]
    omega

theorem values {n : ℕ} (model : RationalCostModel) (A B : ℕ) (h : A ≤ B) (v : FixedArrayTable n ℚ) :
    (GeneralPaperValueInputWordLength.run model A v).2 ≤ (GeneralPaperValueInputWordLength.run model B v).2 := by
  have hs := value_scan model A B h v (List.finRange n)
  have hi : GeneralPaperEqualRouteConstruction.indicesWork A n ≤ GeneralPaperEqualRouteConstruction.indicesWork B n := by
    unfold GeneralPaperEqualRouteConstruction.indicesWork
    gcongr
  dsimp only [GeneralPaperValueInputWordLength.run]
  omega

theorem reference (model : RationalCostModel) (A B : ℕ) (h : A ≤ B) (K n k S b E : ℕ) :
    (GeneralPaperEqualReferenceConstruction.run model A K n k S b E).2 ≤
      (GeneralPaperEqualReferenceConstruction.run model B K n k S b E).2 := by
  dsimp only [GeneralPaperEqualReferenceConstruction.run, GeneralPaperStoredWordLength.run,
    GeneralPaperEqualAddressConstruction.price]
  omega

theorem measured {n : ℕ} (model : RationalCostModel) (A B : ℕ) (h : A ≤ B) (K k : ℕ)
    (v : FixedArrayTable n ℚ) (budget : ℚ) (words : BinaryAccuracyWords) :
    (GeneralPaperEqualReferenceConstruction.measured model A K k v budget words).2 ≤
      (GeneralPaperEqualReferenceConstruction.measured model B K k v budget words).2 := by
  have hv := values model A B h v
  have hb := rational model A B h budget
  have hn := count A B h words.numerator.bits
  have hd := count A B h words.denominator.bits
  have he := scalar model A B h .add words.numerator.bits.length words.denominator.bits.length
  have hr := reference model A B h K n k (GeneralPaperValueRoundingInputPrice.inputSize v)
    (rationalWordWidth budget) (words.numerator.bits.length + words.denominator.bits.length)
  dsimp only [GeneralPaperEqualReferenceConstruction.measured]
  simp only [GeneralPaperValueInputWordLength.data, GeneralPaperStoredRationalWordLength.data,
    GeneralPaperBinaryAccuracy.count_data, GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply]
  omega

theorem initialization (model : RationalCostModel) (A B K : ℕ) (h : A ≤ B)
    (p : GeneralPaperEqualInputDomain.Input model) :
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 ≤
      (GeneralPaperEqualInputInitialization.prepareReference model B K p).2 := by
  have ha := accuracy A B h p.words
  have hr := measured model A B h K (binaryRatioPrecision p.words.denominator.value p.words.numerator.value)
    p.values p.budget p.words
  dsimp only [GeneralPaperEqualInputInitialization.prepareReference]
  simp only [GeneralPaperBinaryAccuracy.prepare_data]
  omega

end Blotto.GeneralPaperMeasuredInitializerMonotonicity
