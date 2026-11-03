import Blotto.BinaryCanonicalMagnitude
import Blotto.RationalArithmeticProgram

/-! All six retained rational arithmetic opcodes have Boolean implementations.
Every output is reduced and high-zero-trimmed; its stored width is bounded by
the reduced rational result rather than by repeated raw expression growth.
Zero division returns canonical 0/1. Cost/whole-register refinement remains
explicitly separate from these opcode semantics and canonical word bounds. -/

namespace Blotto.BinaryRationalOpcode
open BinaryRationalNormalization

def Valid (word : SignedWord) : Prop := 0 < BinaryBigEndian.littleValue word.denominator

def trimWord (word : SignedWord) : SignedWord :=
  ⟨word.negative, BinaryCanonicalMagnitude.trim word.numerator, BinaryCanonicalMagnitude.trim word.denominator⟩

theorem trimWord_value (word : SignedWord) : value (trimWord word) = value word := by
  simp only [trimWord, value, BinaryCanonicalMagnitude.trim_value]

theorem trimWord_valid (word : SignedWord) (h : Valid word) : Valid (trimWord word) := by
  change 0 < BinaryBigEndian.littleValue (BinaryCanonicalMagnitude.trim word.denominator)
  rw [BinaryCanonicalMagnitude.trim_value]
  exact h

def canonicalize (word : SignedWord) : SignedWord := trimWord (normalize word)

theorem canonicalize_value (word : SignedWord) (h : Valid word) : value (canonicalize word) = value word := by
  rw [canonicalize, trimWord_value, normalize_value word h]

theorem canonicalize_valid (word : SignedWord) (h : Valid word) : Valid (canonicalize word) :=
  trimWord_valid _ (normalize_denominator_positive word h)

theorem canonicalize_coprime (word : SignedWord) (h : Valid word) :
    Nat.Coprime (BinaryBigEndian.littleValue (canonicalize word).numerator)
      (BinaryBigEndian.littleValue (canonicalize word).denominator) := by
  change Nat.Coprime (BinaryBigEndian.littleValue (BinaryCanonicalMagnitude.trim (normalize word).numerator))
    (BinaryBigEndian.littleValue (BinaryCanonicalMagnitude.trim (normalize word).denominator))
  rw [BinaryCanonicalMagnitude.trim_value, BinaryCanonicalMagnitude.trim_value]
  exact normalize_coprime word h

theorem value_num_den_of_coprime (word : SignedWord) (hValid : Valid word)
    (hCoprime : Nat.Coprime (BinaryBigEndian.littleValue word.numerator) (BinaryBigEndian.littleValue word.denominator)) :
    (value word).num.natAbs = BinaryBigEndian.littleValue word.numerator ∧
      (value word).den = BinaryBigEndian.littleValue word.denominator := by
  let numerator : ℤ := BinarySignedMagnitude.signedValue word.negative (BinaryBigEndian.littleValue word.numerator)
  let denominator : ℤ := BinaryBigEndian.littleValue word.denominator
  have hn : numerator.natAbs = BinaryBigEndian.littleValue word.numerator := by
    dsimp [numerator, BinarySignedMagnitude.signedValue]
    cases word.negative <;> simp
  have hd : denominator.natAbs = BinaryBigEndian.littleValue word.denominator := Int.natAbs_natCast _
  have hp : 0 < denominator := by
    change 0 < (BinaryBigEndian.littleValue word.denominator : ℤ)
    change 0 < BinaryBigEndian.littleValue word.denominator at hValid
    exact_mod_cast hValid
  have hc : Nat.Coprime numerator.natAbs denominator.natAbs := by rw [hn, hd]; exact hCoprime
  have hv : value word = (numerator : ℚ) / (denominator : ℚ) := by
    unfold value
    dsimp [numerator, denominator, BinarySignedMagnitude.signedValue]
    cases word.negative <;> simp
  rw [hv]
  constructor
  · rw [Rat.num_div_eq_of_coprime hp hc, hn]
  · have he := Rat.den_div_eq_of_coprime hp hc
    change (((numerator : ℚ) / (denominator : ℚ)).den : ℤ) = (BinaryBigEndian.littleValue word.denominator : ℤ) at he
    exact_mod_cast he

theorem canonicalize_width (word : SignedWord) (h : Valid word) :
    width (canonicalize word) ≤ rationalWordWidth (value word) := by
  have hc := value_num_den_of_coprime (canonicalize word) (canonicalize_valid word h) (canonicalize_coprime word h)
  rw [canonicalize_value word h] at hc
  have hN := hc.1.symm
  have hD := hc.2.symm
  have hn := BinaryCanonicalMagnitude.trim_wordWidth (normalize word).numerator
  have hd := BinaryCanonicalMagnitude.trim_wordWidth (normalize word).denominator
  unfold canonicalize trimWord width
  dsimp only
  rw [← BinaryCanonicalMagnitude.trim_value (normalize word).numerator] at hn
  rw [← BinaryCanonicalMagnitude.trim_value (normalize word).denominator] at hd
  change (BinaryCanonicalMagnitude.trim (normalize word).numerator).length ≤ binaryWordWidth (BinaryBigEndian.littleValue (canonicalize word).numerator) at hn
  change (BinaryCanonicalMagnitude.trim (normalize word).denominator).length ≤ binaryWordWidth (BinaryBigEndian.littleValue (canonicalize word).denominator) at hd
  rw [hN] at hn
  rw [hD] at hd
  unfold rationalWordWidth
  omega

def zero : SignedWord := ⟨false, [], [true]⟩

theorem zero_valid : Valid zero := by change (0 : ℕ) < 1; decide
theorem zero_value : value zero = 0 := by simp [zero, value, BinaryBigEndian.littleValue]

def rawApply : RealArithmeticOp → SignedWord → SignedWord → SignedWord
  | .add, first, second => BinaryRationalArithmetic.rawAdd first second
  | .sub, first, second => BinaryRationalArithmetic.rawAdd first (BinaryRationalArithmetic.negate second)
  | .mul, first, second => BinaryRationalArithmetic.rawMultiply first second
  | .div, first, second => if BinaryEuclideanGCD.nonzero second.numerator then BinaryRationalArithmetic.rawDivide first second else zero
  | .minimum, first, second => if BinaryRationalArithmetic.lessEqual first second then first else second
  | .maximum, first, second => if BinaryRationalArithmetic.lessEqual first second then second else first

theorem rawApply_valid (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    Valid (rawApply op first second) := by
  cases op
  · exact BinaryRationalArithmetic.rawAdd_denominator_positive first second hA hB
  · exact BinaryRationalArithmetic.rawAdd_denominator_positive first (BinaryRationalArithmetic.negate second) hA hB
  · exact BinaryRationalArithmetic.rawMultiply_denominator_positive first second hA hB
  · change Valid (if BinaryEuclideanGCD.nonzero second.numerator then BinaryRationalArithmetic.rawDivide first second else zero)
    split
    · rename_i hN
      exact BinaryRationalArithmetic.rawDivide_denominator_positive first second hA ((BinaryEuclideanGCD.nonzero_true_iff _).mp hN)
    · exact zero_valid
  · change Valid (if BinaryRationalArithmetic.lessEqual first second then first else second)
    split <;> assumption
  · change Valid (if BinaryRationalArithmetic.lessEqual first second then second else first)
    split <;> assumption

theorem rawApply_value (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    value (rawApply op first second) = op.applyRat (value first) (value second) := by
  cases op
  · exact BinaryRationalArithmetic.rawAdd_value first second hA hB
  · rw [rawApply, BinaryRationalArithmetic.rawAdd_value first (BinaryRationalArithmetic.negate second) hA hB,
      BinaryRationalArithmetic.negate_value]
    simp only [RealArithmeticOp.applyRat]
    ring
  · exact BinaryRationalArithmetic.rawMultiply_value first second
  · change value (if BinaryEuclideanGCD.nonzero second.numerator then BinaryRationalArithmetic.rawDivide first second else zero) = _
    split
    · exact BinaryRationalArithmetic.rawDivide_value first second
    · rename_i hN
      have hz : BinaryBigEndian.littleValue second.numerator = 0 := by
        apply (BinaryEuclideanGCD.nonzero_false_iff _).mp
        cases h : BinaryEuclideanGCD.nonzero second.numerator <;> simp_all
      have hv : value second = 0 := by
        unfold value
        rw [hz]
        cases second.negative <;> simp
      rw [zero_value, hv]
      simp [RealArithmeticOp.applyRat]
  · change value (if BinaryRationalArithmetic.lessEqual first second then first else second) = min (value first) (value second)
    split
    · rename_i h
      have he := (BinaryRationalArithmetic.lessEqual_iff first second hA hB).mp h
      exact (min_eq_left he).symm
    · rename_i h
      have he : value second ≤ value first := le_of_not_ge (fun hle => h ((BinaryRationalArithmetic.lessEqual_iff first second hA hB).mpr hle))
      exact (min_eq_right he).symm
  · change value (if BinaryRationalArithmetic.lessEqual first second then second else first) = max (value first) (value second)
    split
    · rename_i h
      have he := (BinaryRationalArithmetic.lessEqual_iff first second hA hB).mp h
      exact (max_eq_right he).symm
    · rename_i h
      have he : value second ≤ value first := le_of_not_ge (fun hle => h ((BinaryRationalArithmetic.lessEqual_iff first second hA hB).mpr hle))
      exact (max_eq_left he).symm

def apply (op : RealArithmeticOp) (first second : SignedWord) : SignedWord := canonicalize (rawApply op first second)

theorem apply_value (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    value (apply op first second) = op.applyRat (value first) (value second) :=
  (canonicalize_value _ (rawApply_valid op first second hA hB)).trans (rawApply_value op first second hA hB)

theorem apply_valid (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    Valid (apply op first second) := canonicalize_valid _ (rawApply_valid op first second hA hB)

theorem apply_width (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    width (apply op first second) ≤ rationalWordWidth (op.applyRat (value first) (value second)) := by
  have h := canonicalize_width (rawApply op first second) (rawApply_valid op first second hA hB)
  rw [rawApply_value op first second hA hB] at h
  exact h

theorem apply_height_width (op : RealArithmeticOp) (first second : SignedWord) (hA : Valid first) (hB : Valid second)
    (s : ℕ) (hHeight : RationalHeight (op.applyRat (value first) (value second)) s) :
    width (apply op first second) ≤ 1 + 2 * s :=
  (apply_width op first second hA hB).trans (rationalWordWidth_of_height hHeight)

abbrev ValidWord := {word : SignedWord // Valid word}

def applyValid (op : RealArithmeticOp) (first second : ValidWord) : ValidWord :=
  ⟨apply op first.val second.val, apply_valid op first.val second.val first.property second.property⟩

theorem applyValid_value (op : RealArithmeticOp) (first second : ValidWord) :
    value (applyValid op first second).val = op.applyRat (value first.val) (value second.val) :=
  apply_value op first.val second.val first.property second.property

theorem applyValid_height_width (op : RealArithmeticOp) (first second : ValidWord) (s : ℕ)
    (h : RationalHeight (op.applyRat (value first.val) (value second.val)) s) :
    width (applyValid op first second).val ≤ 1 + 2 * s :=
  apply_height_width op first.val second.val first.property second.property s h

def canonicalizeWithWork (word : SignedWord) : SignedWord × ℕ :=
  let result := normalizeWithWork word
  (trimWord result.1, result.2 + BinaryCanonicalMagnitude.bitWork result.1.numerator +
    BinaryCanonicalMagnitude.bitWork result.1.denominator + 2)

theorem canonicalizeWithWork_state (word : SignedWord) : (canonicalizeWithWork word).1 = canonicalize word := rfl

theorem canonicalizeWithWork_bound (word : SignedWord) :
    (canonicalizeWithWork word).2 ≤ 170 * (width word + 1) ^ 3 := by
  have hN := normalizeWithWork_bound word
  have hNum := BinaryCanonicalMagnitude.bitWork_bound (normalize word).numerator
  have hDen := BinaryCanonicalMagnitude.bitWork_bound (normalize word).denominator
  rw [(normalize_lengths word).1] at hNum
  rw [(normalize_lengths word).2] at hDen
  have hn : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hd : word.denominator.length ≤ width word := Nat.le_max_right _ _
  have hp : 1 ≤ (width word + 1) ^ 3 := one_le_pow₀ (by omega)
  have hLinear : width word + 1 ≤ (width word + 1) ^ 3 := by
    have hSquare : 1 ≤ (width word + 1) ^ 2 := one_le_pow₀ (by omega)
    nlinarith
  unfold canonicalizeWithWork
  dsimp only
  change (normalizeWithWork word).2 + BinaryCanonicalMagnitude.bitWork (normalize word).numerator +
    BinaryCanonicalMagnitude.bitWork (normalize word).denominator + 2 ≤ _
  nlinarith

def rawApplyWork : RealArithmeticOp → SignedWord → SignedWord → ℕ
  | .add, first, second => BinaryRationalArithmetic.rawAddWork first second
  | .sub, first, second => 1 + BinaryRationalArithmetic.rawAddWork first (BinaryRationalArithmetic.negate second)
  | .mul, first, second => BinaryRationalArithmetic.rawMultiplyWork first second
  | .div, first, second => 3 * (second.numerator.length + 1) + 2 +
      if BinaryEuclideanGCD.nonzero second.numerator then BinaryRationalArithmetic.rawDivideWork first second else 2
  | .minimum, first, second => BinaryRationalArithmetic.lessEqualWork first second + 2
  | .maximum, first, second => BinaryRationalArithmetic.lessEqualWork first second + 2

theorem rawApplyWork_bound (op : RealArithmeticOp) (first second : SignedWord) :
    rawApplyWork op first second ≤ 510 * (BinaryRationalArithmetic.pairWidth first second + 1) ^ 2 := by
  have hA := BinaryRationalArithmetic.rawAddWork_bound first second
  have hS := BinaryRationalArithmetic.rawAddWork_bound first (BinaryRationalArithmetic.negate second)
  change _ ≤ 500 * (BinaryRationalArithmetic.pairWidth first second + 1) ^ 2 at hS
  have hM := BinaryRationalArithmetic.rawMultiplyWork_bound first second
  have hD := BinaryRationalArithmetic.rawDivideWork_bound first second
  have hC := BinaryRationalArithmetic.lessEqualWork_bound first second
  have hW := (BinaryRationalArithmetic.operand_widths first second).2.2.1
  cases op <;> simp only [rawApplyWork]
  all_goals try split
  all_goals nlinarith

theorem rawApply_width (op : RealArithmeticOp) (first second : SignedWord) :
    width (rawApply op first second) ≤ 3 * BinaryRationalArithmetic.pairWidth first second + 1 := by
  have hA := BinaryRationalArithmetic.rawAdd_width first second
  have hS := BinaryRationalArithmetic.rawAdd_width first (BinaryRationalArithmetic.negate second)
  change _ ≤ 3 * BinaryRationalArithmetic.pairWidth first second + 1 at hS
  have hM := BinaryRationalArithmetic.rawMultiply_width first second
  have hD := BinaryRationalArithmetic.rawDivide_width first second
  have hFirst : width first ≤ BinaryRationalArithmetic.pairWidth first second := Nat.le_max_left _ _
  have hSecond : width second ≤ BinaryRationalArithmetic.pairWidth first second := Nat.le_max_right _ _
  cases op
  · exact hA
  · exact hS
  · exact hM.trans (Nat.le_succ _)
  · change width (if BinaryEuclideanGCD.nonzero second.numerator then BinaryRationalArithmetic.rawDivide first second else zero) ≤ _
    split
    · exact hD.trans (Nat.le_succ _)
    · change 1 ≤ _
      omega
  · change width (if BinaryRationalArithmetic.lessEqual first second then first else second) ≤ _
    split <;> omega
  · change width (if BinaryRationalArithmetic.lessEqual first second then second else first) ≤ _
    split <;> omega

def applyWithWork (op : RealArithmeticOp) (first second : SignedWord) : SignedWord × ℕ :=
  let result := canonicalizeWithWork (rawApply op first second)
  (result.1, rawApplyWork op first second + result.2)

theorem applyWithWork_state (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithWork op first second).1 = apply op first second := rfl

theorem applyWithWork_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithWork op first second).2 ≤ 12000 * (BinaryRationalArithmetic.pairWidth first second + 1) ^ 3 := by
  have hR := rawApplyWork_bound op first second
  have hC := canonicalizeWithWork_bound (rawApply op first second)
  have hW := rawApply_width op first second
  have hWidth : width (rawApply op first second) + 1 ≤ 4 * (BinaryRationalArithmetic.pairWidth first second + 1) := by omega
  have hPow := Nat.pow_le_pow_left hWidth 3
  have hPrice := hC.trans (Nat.mul_le_mul_left 170 hPow)
  unfold applyWithWork
  dsimp only
  nlinarith

end Blotto.BinaryRationalOpcode
