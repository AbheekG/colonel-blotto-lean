import Blotto.GeneralPaperValueInputWordLength

/-! Construct a reference from measured original value/budget/accuracy
lengths, stored n and the already computed precision exponent. The only
constant K is fixed once for the arithmetic model. No source profile or
mathematical operation price is queried to choose the returned word. -/
namespace Blotto.GeneralPaperEqualReferenceConstruction
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def log (n k S b E : ℕ) : ℕ := 128 + k + binaryWordWidth (S + b + n + E + 1)

def cap (K n k S b E : ℕ) : ℕ := (K + 1) * (128 + k + S + b + n + E + 2)

def run (model : RationalCostModel) (A K n k S b E : ℕ) : ℕ × ℕ :=
  let s0 := S + b
  let s1 := s0 + n
  let s2 := s1 + E
  let total := s2 + 1
  let counted := GeneralPaperStoredWordLength.run A total
  let base := 128 + k
  let L := base + counted.1
  let W := K * L
  (W, GeneralPaperEqualAddressConstruction.price model A S b s0 +
    GeneralPaperEqualAddressConstruction.price model A s0 n s1 +
    GeneralPaperEqualAddressConstruction.price model A s1 E s2 +
    GeneralPaperEqualAddressConstruction.price model A s2 1 total + counted.2 +
    GeneralPaperEqualAddressConstruction.price model A 128 k base +
    GeneralPaperEqualAddressConstruction.price model A base counted.1 L +
    GeneralPaperEqualAddressConstruction.price model A K L W + 128 * A + 128)

theorem data (model : RationalCostModel) (A K n k S b E : ℕ) :
    (run model A K n k S b E).1 = K * log n k S b E := rfl

def profile (model : RationalCostModel) (A K n k S b E : ℕ) : ℕ :=
  1024 * (A + model.rat (1 + binaryWordWidth (cap K n k S b E)) + 1)

theorem work (model : RationalCostModel) (A K n k S b E : ℕ) :
    (run model A K n k S b E).2 ≤ profile model A K n k S b E := by
  let C := cap K n k S b E
  let B := 128 + k + S + b + n + E + 2
  have hB : B ≤ C := by
    change B ≤ (K + 1) * B
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hK : K ≤ C := by
    have h := Nat.le_mul_of_pos_right (K + 1) (show 0 < B by dsimp [B]; omega)
    dsimp only [C, cap] at *
    dsimp only [B] at h
    omega
  have hSum : S + b + n + E + 1 ≤ C := by dsimp [B] at hB; omega
  have hWord : binaryWordWidth (S + b + n + E + 1) ≤ S + b + n + E + 2 := by
    have h := Nat.log2_le_self (S + b + n + E + 1)
    unfold binaryWordWidth
    omega
  have hL : log n k S b E ≤ B := by dsimp [log, B]; omega
  have hW : K * log n k S b E ≤ C := by
    have h := Nat.mul_le_mul_left K hL
    change K * log n k S b E ≤ (K + 1) * B
    nlinarith only [h]
  have hPrice (a c out : ℕ) (ha : a ≤ C) (hc : c ≤ C) (ho : out ≤ C) :
      GeneralPaperEqualAddressConstruction.price model A a c out ≤
        5 * model.rat (1 + binaryWordWidth C) + 16 * A + 16 :=
    GeneralPaperEqualAddressConstruction.price_work model A a c out (1 + binaryWordWidth C)
      (Nat.add_le_add_left (binaryWordWidth_mono ha) 1)
      (Nat.add_le_add_left (binaryWordWidth_mono hc) 1)
      (Nat.add_le_add_left (binaryWordWidth_mono ho) 1)
  have h0 := hPrice S b (S + b) (by omega) (by omega) (by omega)
  have h1 := hPrice (S + b) n (S + b + n) (by omega) (by omega) (by omega)
  have h2 := hPrice (S + b + n) E (S + b + n + E) (by omega) (by omega) (by omega)
  have h3 := hPrice (S + b + n + E) 1 (S + b + n + E + 1) (by omega) (by omega) hSum
  have h4 := hPrice 128 k (128 + k) (by dsimp [B] at hB; omega)
    (by dsimp [B] at hB; omega) (by dsimp [B] at hB; omega)
  have h5 := hPrice (128 + k) (binaryWordWidth (S + b + n + E + 1)) (log n k S b E)
    (by dsimp [B] at hB; omega) (by omega) (hL.trans hB)
  have h6 := hPrice K (log n k S b E) (K * log n k S b E) hK (hL.trans hB) hW
  have hCount := GeneralPaperStoredWordLength.work A (S + b + n + E + 1)
  have hCountWord := binaryWordWidth_mono hSum
  have hRat := model.word_le (1 + binaryWordWidth C)
  unfold run profile
  dsimp only [GeneralPaperStoredWordLength.data]
  change _ ≤ 1024 * (A + model.rat (1 + binaryWordWidth C) + 1)
  change GeneralPaperEqualAddressConstruction.price model A S b (S + b) +
    GeneralPaperEqualAddressConstruction.price model A (S + b) n (S + b + n) +
    GeneralPaperEqualAddressConstruction.price model A (S + b + n) E (S + b + n + E) +
    GeneralPaperEqualAddressConstruction.price model A (S + b + n + E) 1 (S + b + n + E + 1) +
    (GeneralPaperStoredWordLength.run A (S + b + n + E + 1)).2 +
    GeneralPaperEqualAddressConstruction.price model A 128 k (128 + k) +
    GeneralPaperEqualAddressConstruction.price model A (128 + k) (binaryWordWidth (S + b + n + E + 1)) (log n k S b E) +
    GeneralPaperEqualAddressConstruction.price model A K (log n k S b E) (K * log n k S b E) + 128 * A + 128 ≤ _
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, hCount, hCountWord, hRat]

def measured {n : ℕ} (model : RationalCostModel) (A K k : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) (words : BinaryAccuracyWords) : ℕ × ℕ :=
  let valuesLength := GeneralPaperValueInputWordLength.run model A values
  let budgetLength := GeneralPaperStoredRationalWordLength.run model A budget
  let numerator := GeneralPaperBinaryAccuracy.count id A words.numerator.bits
  let denominator := GeneralPaperBinaryAccuracy.count id A words.denominator.bits
  let E := GeneralPaperNaturalScalarStep.run model A .add numerator.1 denominator.1
  let built := run model A K n k valuesLength.1 budgetLength.1 E.1
  (built.1, valuesLength.2 + budgetLength.2 + numerator.2 + denominator.2 + E.2 + built.2 + 128 * A + 128)

theorem measured_data {n : ℕ} (model : RationalCostModel) (A K k : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) (words : BinaryAccuracyWords) :
    (measured model A K k values budget words).1 = K * log n k
      (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget)
      (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) := by
  simp only [measured, data, GeneralPaperValueInputWordLength.data, GeneralPaperStoredRationalWordLength.data,
    GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply, GeneralPaperBinaryAccuracy.count_data,
    PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons, GeneralPaperBinaryAccuracyConstructionStorage.inputSize]
  congr 2
  omega


def measuredProfile (model : RationalCostModel) (A K n k S b E : ℕ) : ℕ :=
  GeneralPaperValueInputWordLength.profile model A n S +
    GeneralPaperWordLengthLifetime.rationalProfile model A b +
    2 * GeneralPaperAccuracyCountConstructionStorage.price A E +
    5 * model.rat (1 + binaryWordWidth E) + 16 * A + 16 +
    profile model A K n k S b E + 128 * A + 128

theorem measured_work {n : ℕ} (model : RationalCostModel) (A K k : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) (words : BinaryAccuracyWords) :
    (measured model A K k values budget words).2 ≤ measuredProfile model A K n k
      (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget)
      (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) := by
  let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize words
  have hN : (GeneralPaperBinaryAccuracy.count id A words.numerator.bits).1 = words.numerator.width := by
    simp only [GeneralPaperBinaryAccuracy.count_data, PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons]
  have hD : (GeneralPaperBinaryAccuracy.count id A words.denominator.bits).1 = words.denominator.width := by
    simp only [GeneralPaperBinaryAccuracy.count_data, PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons]
  have hSum : words.numerator.width + words.denominator.width = E := by
    dsimp [E, GeneralPaperBinaryAccuracyConstructionStorage.inputSize]
    omega
  have hE : (GeneralPaperNaturalScalarStep.run model A .add words.numerator.width words.denominator.width).1 = E := hSum
  have hNWork := GeneralPaperAccuracyCountConstructionStorage.work_cap A E words.numerator.bits (by
    simp only [PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons] at hSum ⊢
    omega)
  have hDWork := GeneralPaperAccuracyCountConstructionStorage.work_cap A E words.denominator.bits (by
    simp only [PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons] at hSum ⊢
    omega)
  change (GeneralPaperBinaryAccuracy.count id A words.numerator.bits).2 ≤
    GeneralPaperAccuracyCountConstructionStorage.price A E at hNWork
  change (GeneralPaperBinaryAccuracy.count id A words.denominator.bits).2 ≤
    GeneralPaperAccuracyCountConstructionStorage.price A E at hDWork
  have hn := binaryWordWidth_mono (show words.numerator.width ≤ E by omega)
  have hd := binaryWordWidth_mono (show words.denominator.width ≤ E by omega)
  have hJoin := GeneralPaperNaturalScalarStep.work model A .add words.numerator.width words.denominator.width
    (1 + binaryWordWidth E)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by change 1 + binaryWordWidth (words.numerator.width + words.denominator.width) ≤ _; rw [hSum])
  have hValues := GeneralPaperValueInputWordLength.work model A values
  have hBudget := GeneralPaperStoredRationalWordLength.work model A budget
  have hBuilt := work model A K n k (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget) E
  simp only [measured, GeneralPaperValueInputWordLength.data, GeneralPaperStoredRationalWordLength.data, hN, hD, hE]
  change _ ≤ GeneralPaperValueInputWordLength.profile model A n (GeneralPaperValueRoundingInputPrice.inputSize values) +
    GeneralPaperWordLengthLifetime.rationalProfile model A (rationalWordWidth budget) +
    2 * GeneralPaperAccuracyCountConstructionStorage.price A E + 5 * model.rat (1 + binaryWordWidth E) +
    16 * A + 16 + profile model A K n k (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget) E + 128 * A + 128
  unfold GeneralPaperWordLengthLifetime.rationalProfile
  nlinarith only [hValues, hBudget, hNWork, hDWork, hJoin, hBuilt]

end Blotto.GeneralPaperEqualReferenceConstruction
