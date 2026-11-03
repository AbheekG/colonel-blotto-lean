import Blotto.BinaryEuclideanGCD

/-! Canonical signed rational data are normalized with Boolean GCD and two
Boolean long divisions. Runtime never constructs a Rat or calls numeric gcd,
division, remainder or multiplication on represented values. Rational values,
coprimality and canonical signs below are proof specifications. The explicit
schoolbook Boolean/cell work bound is separate from a compiler/GC guarantee. -/

namespace Blotto.BinaryRationalNormalization

structure SignedWord where
  negative : Bool
  numerator : List Bool
  denominator : List Bool

noncomputable def value (word : SignedWord) : ℚ :=
  (if word.negative then -(BinaryBigEndian.littleValue word.numerator : ℚ)
    else (BinaryBigEndian.littleValue word.numerator : ℚ)) / BinaryBigEndian.littleValue word.denominator

def width (word : SignedWord) : ℕ := max word.numerator.length word.denominator.length

def normalizeWithWork (word : SignedWord) : SignedWord × ℕ :=
  let common := BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator
  let numerator := BinaryLongDivision.divideWithWork word.numerator common.1
  let denominator := BinaryLongDivision.divideWithWork word.denominator common.1
  let sign := word.negative && BinaryEuclideanGCD.nonzero numerator.1.1
  (⟨sign, numerator.1.1, denominator.1.1⟩,
    common.2 + numerator.2 + denominator.2 + 3 * (word.numerator.length + 1) + 2)

def normalize (word : SignedWord) : SignedWord := (normalizeWithWork word).1

theorem common_positive (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    0 < BinaryBigEndian.littleValue (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1 := by
  rw [BinaryEuclideanGCD.gcdWithWork_value]
  exact Nat.gcd_pos_of_pos_right _ hD

theorem normalize_numerator_value (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    BinaryBigEndian.littleValue (normalize word).numerator =
      BinaryBigEndian.littleValue word.numerator /
        Nat.gcd (BinaryBigEndian.littleValue word.numerator) (BinaryBigEndian.littleValue word.denominator) := by
  change BinaryBigEndian.littleValue
    (BinaryLongDivision.divideWithWork word.numerator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.1 = _
  rw [BinaryLongDivision.divideWithWork_refines]
  rw [(BinaryLongDivision.divide_div_mod _ _ (common_positive word hD)).1,
    BinaryEuclideanGCD.gcdWithWork_value]

theorem normalize_denominator_value (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    BinaryBigEndian.littleValue (normalize word).denominator =
      BinaryBigEndian.littleValue word.denominator /
        Nat.gcd (BinaryBigEndian.littleValue word.numerator) (BinaryBigEndian.littleValue word.denominator) := by
  change BinaryBigEndian.littleValue
    (BinaryLongDivision.divideWithWork word.denominator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.1 = _
  rw [BinaryLongDivision.divideWithWork_refines]
  rw [(BinaryLongDivision.divide_div_mod _ _ (common_positive word hD)).1,
    BinaryEuclideanGCD.gcdWithWork_value]

theorem normalize_denominator_positive (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    0 < BinaryBigEndian.littleValue (normalize word).denominator := by
  rw [normalize_denominator_value word hD]
  exact Nat.div_pos (Nat.gcd_le_right _ hD) (Nat.gcd_pos_of_pos_right _ hD)

theorem normalize_coprime (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    Nat.Coprime (BinaryBigEndian.littleValue (normalize word).numerator)
      (BinaryBigEndian.littleValue (normalize word).denominator) := by
  rw [normalize_numerator_value word hD, normalize_denominator_value word hD]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hD)

theorem normalization_divisions_exact (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    BinaryBigEndian.littleValue (BinaryLongDivision.divideWithWork word.numerator
        (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.2 = 0 ∧
      BinaryBigEndian.littleValue (BinaryLongDivision.divideWithWork word.denominator
        (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.2 = 0 := by
  rw [BinaryLongDivision.divideWithWork_refines, BinaryLongDivision.divideWithWork_refines]
  rw [(BinaryLongDivision.divide_div_mod _ _ (common_positive word hD)).2,
    (BinaryLongDivision.divide_div_mod _ _ (common_positive word hD)).2,
    BinaryEuclideanGCD.gcdWithWork_value]
  exact ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left _ _), Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right _ _)⟩

theorem normalize_sign (word : SignedWord) :
    (normalize word).negative = (word.negative && BinaryEuclideanGCD.nonzero (normalize word).numerator) := rfl

theorem normalize_zero_sign (word : SignedWord)
    (hZero : BinaryBigEndian.littleValue (normalize word).numerator = 0) :
    (normalize word).negative = false := by
  rw [normalize_sign, (BinaryEuclideanGCD.nonzero_false_iff _).mpr hZero]
  simp

theorem normalize_zero_denominator_one (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator)
    (hZero : BinaryBigEndian.littleValue word.numerator = 0) :
    BinaryBigEndian.littleValue (normalize word).denominator = 1 := by
  rw [normalize_denominator_value word hD, hZero, Nat.gcd_zero_left, Nat.div_self hD]

theorem signed_magnitude_preserved (word : SignedWord) :
    (if (normalize word).negative then -(BinaryBigEndian.littleValue (normalize word).numerator : ℚ)
      else (BinaryBigEndian.littleValue (normalize word).numerator : ℚ)) =
    (if word.negative then -(BinaryBigEndian.littleValue (normalize word).numerator : ℚ)
      else (BinaryBigEndian.littleValue (normalize word).numerator : ℚ)) := by
  rw [normalize_sign]
  by_cases h : BinaryEuclideanGCD.nonzero (normalize word).numerator = true
  · rw [h]
    cases word.negative <;> rfl
  · have hz : BinaryBigEndian.littleValue (normalize word).numerator = 0 := by
      apply (BinaryEuclideanGCD.nonzero_false_iff _).mp
      cases he : BinaryEuclideanGCD.nonzero (normalize word).numerator <;> simp_all
    rw [hz]
    cases word.negative <;> simp

theorem normalize_value (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) : value (normalize word) = value word := by
  let N := BinaryBigEndian.littleValue word.numerator
  let D := BinaryBigEndian.littleValue word.denominator
  let G := Nat.gcd N D
  have hG : (0 : ℚ) < G := by exact_mod_cast Nat.gcd_pos_of_pos_right N hD
  have hGN : G ∣ N := Nat.gcd_dvd_left N D
  have hGD : G ∣ D := Nat.gcd_dvd_right N D
  have hDN : (0 : ℚ) < D := by exact_mod_cast hD
  unfold value
  rw [signed_magnitude_preserved, normalize_numerator_value word hD, normalize_denominator_value word hD]
  change (if word.negative then -((N / G : ℕ) : ℚ) else ((N / G : ℕ) : ℚ)) /
      ((D / G : ℕ) : ℚ) = (if word.negative then -(N : ℚ) else (N : ℚ)) / D
  rw [Nat.cast_div hGN (ne_of_gt hG), Nat.cast_div hGD (ne_of_gt hG)]
  cases word.negative <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> field_simp

theorem normalize_lengths (word : SignedWord) :
    (normalize word).numerator.length = word.numerator.length ∧
      (normalize word).denominator.length = word.denominator.length := by
  constructor
  · change (BinaryLongDivision.divideWithWork word.numerator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.1.length = _
    rw [BinaryLongDivision.divideWithWork_refines]
    exact (BinaryLongDivision.divide_lengths _ _).1
  · change (BinaryLongDivision.divideWithWork word.denominator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1).1.1.length = _
    rw [BinaryLongDivision.divideWithWork_refines]
    exact (BinaryLongDivision.divide_lengths _ _).1

theorem normalize_word_bounds (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    BinaryBigEndian.littleValue (normalize word).numerator ≤ BinaryBigEndian.littleValue word.numerator ∧
      BinaryBigEndian.littleValue (normalize word).denominator ≤ BinaryBigEndian.littleValue word.denominator := by
  rw [normalize_numerator_value word hD, normalize_denominator_value word hD]
  exact ⟨Nat.div_le_self _ _, Nat.div_le_self _ _⟩

theorem normalizeWithWork_bound (word : SignedWord) :
    (normalizeWithWork word).2 ≤ 150 * (width word + 1) ^ 3 := by
  have hG := BinaryEuclideanGCD.gcdWithWork_bound word.numerator word.denominator
  have hGL := BinaryEuclideanGCD.gcdWithWork_length word.numerator word.denominator
  have hN := BinaryLongDivision.bitWork_quadratic word.numerator
    (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1
  have hD := BinaryLongDivision.bitWork_quadratic word.denominator
    (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1
  have hNW : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hDW : word.denominator.length ≤ width word := Nat.le_max_right _ _
  change (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1.length ≤ width word at hGL
  change (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).2 ≤ 80 * (width word + 1) ^ 3 at hG
  have hNB : BinaryLongDivision.bitWork word.numerator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1 ≤ 30 * (width word + 1) ^ 2 := by
    nlinarith
  have hDB : BinaryLongDivision.bitWork word.denominator
      (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1 ≤ 30 * (width word + 1) ^ 2 := by
    nlinarith
  unfold normalizeWithWork
  dsimp only
  rw [BinaryLongDivision.divideWithWork_refines, BinaryLongDivision.divideWithWork_refines]
  dsimp only
  nlinarith

theorem normalizeWithWork_contract (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    value (normalizeWithWork word).1 = value word ∧
      0 < BinaryBigEndian.littleValue (normalizeWithWork word).1.denominator ∧
      Nat.Coprime (BinaryBigEndian.littleValue (normalizeWithWork word).1.numerator)
        (BinaryBigEndian.littleValue (normalizeWithWork word).1.denominator) ∧
      (BinaryBigEndian.littleValue (normalizeWithWork word).1.numerator = 0 →
        (normalizeWithWork word).1.negative = false) ∧
      (normalizeWithWork word).2 ≤ 150 * (width word + 1) ^ 3 :=
  ⟨normalize_value word hD, normalize_denominator_positive word hD, normalize_coprime word hD,
    normalize_zero_sign word, normalizeWithWork_bound word⟩

end Blotto.BinaryRationalNormalization
