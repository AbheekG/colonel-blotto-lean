import Blotto.BinarySteinGCD

/-! Boolean Stein GCD and two existing Boolean long divisions normalize the
same stored signed rational words as the retained Euclidean backend. Exact
raw and canonical bytes are proved for every valid denominator; the derived
work bounds are quadratic and include GCD, divisions, sign scan and trimming.
The annotations are erasable Boolean/list-cell work; complete caller machine
and storage composition remain separate. -/

namespace Blotto.BinaryQuadraticNormalization
open BinaryRationalNormalization BinaryRationalOpcode

theorem quotient_eq_of_divisor_value (dividend first second : List Bool)
    (hFirst : 0 < BinaryBigEndian.littleValue first)
    (hValue : BinaryBigEndian.littleValue first = BinaryBigEndian.littleValue second) :
    (BinaryLongDivision.divideWithWork dividend first).1.1 =
      (BinaryLongDivision.divideWithWork dividend second).1.1 := by
  have hSecond : 0 < BinaryBigEndian.littleValue second := by omega
  rw [BinaryLongDivision.divideWithWork_refines,BinaryLongDivision.divideWithWork_refines]
  apply BinaryBorrowWord.littleValue_injective
  · rw [(BinaryLongDivision.divide_lengths dividend first).1,
      (BinaryLongDivision.divide_lengths dividend second).1]
  · rw [(BinaryLongDivision.divide_div_mod dividend first hFirst).1,
      (BinaryLongDivision.divide_div_mod dividend second hSecond).1,hValue]

def normalizeWithWork (word : SignedWord) : SignedWord × ℕ :=
  let common := BinarySteinGCD.gcdWithWork word.numerator word.denominator
  let numerator := BinaryLongDivision.divideWithWork word.numerator common.1
  let denominator := BinaryLongDivision.divideWithWork word.denominator common.1
  let sign := word.negative && BinaryEuclideanGCD.nonzero numerator.1.1
  (⟨sign,numerator.1.1,denominator.1.1⟩,
    common.2+numerator.2+denominator.2+3*(word.numerator.length+1)+2)

theorem normalizeWithWork_state (word : SignedWord) (hValid : Valid word) :
    (normalizeWithWork word).1 = BinaryRationalNormalization.normalize word := by
  have hG : BinaryBigEndian.littleValue (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1 =
      BinaryBigEndian.littleValue (BinaryEuclideanGCD.gcdWithWork word.numerator word.denominator).1 := by
    rw [BinarySteinGCD.gcdWithWork_state,BinarySteinGCD.canonicalGcd_value,BinaryEuclideanGCD.gcdWithWork_value]
  have hp : 0 < BinaryBigEndian.littleValue (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1 := by
    rw [hG]
    exact common_positive word hValid
  have hn := quotient_eq_of_divisor_value word.numerator _ _ hp hG
  have hd := quotient_eq_of_divisor_value word.denominator _ _ hp hG
  unfold normalizeWithWork BinaryRationalNormalization.normalize BinaryRationalNormalization.normalizeWithWork
  dsimp only
  rw [hn,hd]

theorem normalize_lengths (word : SignedWord) :
    (normalizeWithWork word).1.numerator.length = word.numerator.length ∧
      (normalizeWithWork word).1.denominator.length = word.denominator.length := by
  unfold normalizeWithWork
  dsimp only
  rw [BinaryLongDivision.divideWithWork_refines,BinaryLongDivision.divideWithWork_refines]
  exact ⟨(BinaryLongDivision.divide_lengths _ _).1,(BinaryLongDivision.divide_lengths _ _).1⟩

theorem normalizeWithWork_bound (word : SignedWord) :
    (normalizeWithWork word).2 ≤ 500 * (width word + 1) ^ 2 := by
  have hg := BinarySteinGCD.gcdWithWork_bound word.numerator word.denominator
  have hl := BinarySteinGCD.canonicalGcd_length word.numerator word.denominator
  have hn := BinaryLongDivision.bitWork_quadratic word.numerator
    (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1
  have hd := BinaryLongDivision.bitWork_quadratic word.denominator
    (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1
  have ha : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hb : word.denominator.length ≤ width word := Nat.le_max_right _ _
  change (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1.length ≤ width word at hl
  change (BinarySteinGCD.gcdWithWork word.numerator word.denominator).2 ≤ 400 * (width word + 1)^2 at hg
  have hnb : BinaryLongDivision.bitWork word.numerator
      (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1 ≤ 30 * (width word + 1)^2 := by nlinarith
  have hdb : BinaryLongDivision.bitWork word.denominator
      (BinarySteinGCD.gcdWithWork word.numerator word.denominator).1 ≤ 30 * (width word + 1)^2 := by nlinarith
  unfold normalizeWithWork
  dsimp only
  rw [BinaryLongDivision.divideWithWork_refines,BinaryLongDivision.divideWithWork_refines]
  dsimp only
  nlinarith

def canonicalizeWithWork (word : SignedWord) : SignedWord × ℕ :=
  let normalized := normalizeWithWork word
  let numerator := BinaryCanonicalMagnitude.trimWithWork normalized.1.numerator
  let denominator := BinaryCanonicalMagnitude.trimWithWork normalized.1.denominator
  (⟨normalized.1.negative,numerator.1,denominator.1⟩,normalized.2+numerator.2+denominator.2)

theorem canonicalizeWithWork_state (word : SignedWord) (hValid : Valid word) :
    (canonicalizeWithWork word).1 = BinaryRationalOpcode.canonicalize word := by
  unfold canonicalizeWithWork BinaryRationalOpcode.canonicalize BinaryRationalOpcode.trimWord
  dsimp only
  rw [normalizeWithWork_state word hValid]
  rfl

theorem canonicalizeWithWork_bound (word : SignedWord) :
    (canonicalizeWithWork word).2 ≤ 600 * (width word + 1)^2 := by
  have hn := BinaryCanonicalMagnitude.bitWork_bound (normalizeWithWork word).1.numerator
  have hd := BinaryCanonicalMagnitude.bitWork_bound (normalizeWithWork word).1.denominator
  rw [(normalize_lengths word).1] at hn
  rw [(normalize_lengths word).2] at hd
  have hg := normalizeWithWork_bound word
  have ha : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hb : word.denominator.length ≤ width word := Nat.le_max_right _ _
  change (normalizeWithWork word).2 + BinaryCanonicalMagnitude.bitWork (normalizeWithWork word).1.numerator +
    BinaryCanonicalMagnitude.bitWork (normalizeWithWork word).1.denominator ≤ _
  nlinarith

theorem canonicalizeWithWork_contract (word : SignedWord) (hValid : Valid word) :
    (canonicalizeWithWork word).1 = BinaryRationalOpcode.canonicalize word ∧
      value (canonicalizeWithWork word).1 = value word ∧
      BinaryRationalEncoding.CanonicalWord (canonicalizeWithWork word).1 ∧
      (canonicalizeWithWork word).2 ≤ 600 * (width word + 1)^2 := by
  have hs := canonicalizeWithWork_state word hValid
  refine ⟨hs,?_,?_,canonicalizeWithWork_bound word⟩
  · rw [hs]
    exact canonicalize_value word hValid
  · rw [hs]
    exact ⟨canonicalize_valid word hValid,by
      have hw := canonicalize_width word hValid
      rw [← canonicalize_value word hValid] at hw
      exact hw⟩

end Blotto.BinaryQuadraticNormalization
