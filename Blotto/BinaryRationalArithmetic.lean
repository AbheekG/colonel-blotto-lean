import Blotto.BinarySignedMagnitude
import Blotto.RationalCostModel

/-! Boolean rational add/subtract/multiply/divide form signed cross products
and normalize with the verified Boolean backend. Only specifications use ℚ;
runtime representations remain sign and Boolean numerator/denominator lists.
Division requires a positive divisor magnitude. Conservative cubic bit prices
are separate from the earlier quadratic/fast Rat majorants and native GC. -/

namespace Blotto.BinaryRationalArithmetic
open BinaryRationalNormalization

def numeratorWord (word : SignedWord) : BinarySignedMagnitude.Word := ⟨word.negative, word.numerator⟩
def denominatorWord (word : SignedWord) : BinarySignedMagnitude.Word := ⟨false, word.denominator⟩

theorem value_via_integer (word : SignedWord) :
    value word = (BinarySignedMagnitude.value (numeratorWord word) : ℚ) /
      (BinaryBigEndian.littleValue word.denominator : ℚ) := by
  unfold value numeratorWord BinarySignedMagnitude.value BinarySignedMagnitude.signedValue
  cases word.negative <;> simp

theorem denominatorWord_value (word : SignedWord) :
    BinarySignedMagnitude.value (denominatorWord word) = (BinaryBigEndian.littleValue word.denominator : ℤ) := rfl

def rawAdd (first second : SignedWord) : SignedWord :=
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  let numerator := BinarySignedMagnitude.add left right
  ⟨numerator.negative, numerator.bits, BinaryMultiplication.multiply first.denominator second.denominator⟩

def rawMultiply (first second : SignedWord) : SignedWord :=
  let numerator := BinarySignedMagnitude.multiply (numeratorWord first) (numeratorWord second)
  ⟨numerator.negative, numerator.bits, BinaryMultiplication.multiply first.denominator second.denominator⟩

def rawDivide (first second : SignedWord) : SignedWord :=
  ⟨Bool.xor first.negative second.negative,
    BinaryMultiplication.multiply first.numerator second.denominator,
    BinaryMultiplication.multiply first.denominator second.numerator⟩

def negate (word : SignedWord) : SignedWord := ⟨!word.negative, word.numerator, word.denominator⟩

theorem negate_value (word : SignedWord) : value (negate word) = -value word := by
  unfold negate value
  cases word.negative <;> simp
  all_goals ring

theorem rawAdd_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    0 < BinaryBigEndian.littleValue (rawAdd first second).denominator := by
  change 0 < BinaryBigEndian.littleValue (BinaryMultiplication.multiply first.denominator second.denominator)
  rw [BinaryMultiplication.multiply_value]
  exact Nat.mul_pos hA hB

theorem rawMultiply_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    0 < BinaryBigEndian.littleValue (rawMultiply first second).denominator := by
  change 0 < BinaryBigEndian.littleValue (BinaryMultiplication.multiply first.denominator second.denominator)
  rw [BinaryMultiplication.multiply_value]
  exact Nat.mul_pos hA hB

theorem rawDivide_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.numerator) :
    0 < BinaryBigEndian.littleValue (rawDivide first second).denominator := by
  change 0 < BinaryBigEndian.littleValue (BinaryMultiplication.multiply first.denominator second.numerator)
  rw [BinaryMultiplication.multiply_value]
  exact Nat.mul_pos hA hB

theorem rawAdd_value (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    value (rawAdd first second) = value first + value second := by
  rw [value_via_integer (rawAdd first second), value_via_integer first, value_via_integer second]
  change (BinarySignedMagnitude.value (BinarySignedMagnitude.add
      (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
      (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first))) : ℚ) /
    BinaryBigEndian.littleValue (BinaryMultiplication.multiply first.denominator second.denominator) = _
  rw [BinarySignedMagnitude.add_value, BinarySignedMagnitude.multiply_value,
    BinarySignedMagnitude.multiply_value, denominatorWord_value, denominatorWord_value,
    BinaryMultiplication.multiply_value]
  push_cast
  have ha : (BinaryBigEndian.littleValue first.denominator : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hb : (BinaryBigEndian.littleValue second.denominator : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  field_simp

theorem rawMultiply_value (first second : SignedWord) :
    value (rawMultiply first second) = value first * value second := by
  rw [value_via_integer (rawMultiply first second), value_via_integer first, value_via_integer second]
  change (BinarySignedMagnitude.value (BinarySignedMagnitude.multiply (numeratorWord first) (numeratorWord second)) : ℚ) /
      BinaryBigEndian.littleValue (BinaryMultiplication.multiply first.denominator second.denominator) = _
  rw [BinarySignedMagnitude.multiply_value, BinaryMultiplication.multiply_value]
  push_cast
  ring

theorem rawDivide_value (first second : SignedWord) : value (rawDivide first second) = value first / value second := by
  cases first with
  | mk signA numA denA =>
    cases second with
    | mk signB numB denB =>
      cases signA <;> cases signB <;>
        simp [rawDivide, value, BinaryMultiplication.multiply_value, Nat.cast_mul, div_eq_mul_inv, inv_inv]
      all_goals ring

def add (first second : SignedWord) : SignedWord := normalize (rawAdd first second)
def subtract (first second : SignedWord) : SignedWord := add first (negate second)
def multiply (first second : SignedWord) : SignedWord := normalize (rawMultiply first second)
def divide (first second : SignedWord) : SignedWord := normalize (rawDivide first second)

theorem add_value (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) : value (add first second) = value first + value second := by
  rw [add, normalize_value _ (rawAdd_denominator_positive first second hA hB)]
  exact rawAdd_value first second hA hB

theorem subtract_value (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) : value (subtract first second) = value first - value second := by
  rw [subtract, add_value first (negate second) hA hB, negate_value]
  ring

theorem multiply_value (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) : value (multiply first second) = value first * value second := by
  rw [multiply, normalize_value _ (rawMultiply_denominator_positive first second hA hB)]
  exact rawMultiply_value first second

theorem divide_value (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.numerator) : value (divide first second) = value first / value second := by
  rw [divide, normalize_value _ (rawDivide_denominator_positive first second hA hB)]
  exact rawDivide_value first second

def pairWidth (first second : SignedWord) : ℕ := max (width first) (width second)

theorem rawAdd_width (first second : SignedWord) : width (rawAdd first second) ≤ 3 * pairWidth first second + 1 := by
  have ha := BinaryMultiplication.multiply_length first.numerator second.denominator
  have hb := BinaryMultiplication.multiply_length second.numerator first.denominator
  have hd := BinaryMultiplication.multiply_length first.denominator second.denominator
  have hs := BinarySignedMagnitude.add_length
    (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
    (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first))
  unfold rawAdd width
  dsimp only
  unfold pairWidth width at *
  change (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)).bits.length ≤ _ at ha
  change (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)).bits.length ≤ _ at hb
  omega

theorem rawMultiply_width (first second : SignedWord) : width (rawMultiply first second) ≤ 3 * pairWidth first second := by
  have hn := BinaryMultiplication.multiply_length first.numerator second.numerator
  have hd := BinaryMultiplication.multiply_length first.denominator second.denominator
  unfold rawMultiply width pairWidth
  dsimp only [BinarySignedMagnitude.multiply, numeratorWord]
  unfold width
  omega

theorem rawDivide_width (first second : SignedWord) : width (rawDivide first second) ≤ 3 * pairWidth first second := by
  have hn := BinaryMultiplication.multiply_length first.numerator second.denominator
  have hd := BinaryMultiplication.multiply_length first.denominator second.numerator
  unfold rawDivide width pairWidth
  dsimp only
  unfold width
  omega

theorem add_width (first second : SignedWord) : width (add first second) ≤ 3 * pairWidth first second + 1 := by
  have h := normalize_lengths (rawAdd first second)
  unfold add width
  rw [h.1, h.2]
  exact rawAdd_width first second

theorem multiply_width (first second : SignedWord) : width (multiply first second) ≤ 3 * pairWidth first second := by
  have h := normalize_lengths (rawMultiply first second)
  unfold multiply width
  rw [h.1, h.2]
  exact rawMultiply_width first second

theorem divide_width (first second : SignedWord) : width (divide first second) ≤ 3 * pairWidth first second := by
  have h := normalize_lengths (rawDivide first second)
  unfold divide width
  rw [h.1, h.2]
  exact rawDivide_width first second

theorem add_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    0 < BinaryBigEndian.littleValue (add first second).denominator :=
  normalize_denominator_positive _ (rawAdd_denominator_positive first second hA hB)

theorem multiply_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    0 < BinaryBigEndian.littleValue (multiply first second).denominator :=
  normalize_denominator_positive _ (rawMultiply_denominator_positive first second hA hB)

theorem divide_denominator_positive (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.numerator) :
    0 < BinaryBigEndian.littleValue (divide first second).denominator :=
  normalize_denominator_positive _ (rawDivide_denominator_positive first second hA hB)

theorem unsignedMultiplyWork_bound (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    BinaryMultiplication.work a b ≤ 100 * (W + 1) ^ 2 := by
  have h := BinaryMultiplication.work_bound a b
  nlinarith

theorem operand_widths (first second : SignedWord) :
    first.numerator.length ≤ pairWidth first second ∧ first.denominator.length ≤ pairWidth first second ∧
      second.numerator.length ≤ pairWidth first second ∧ second.denominator.length ≤ pairWidth first second := by
  unfold pairWidth width
  omega

def rawAddWork (first second : SignedWord) : ℕ :=
  BinarySignedMagnitude.multiplyWork (numeratorWord first) (denominatorWord second) +
    BinarySignedMagnitude.multiplyWork (numeratorWord second) (denominatorWord first) +
      BinarySignedMagnitude.addWork
        (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
        (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)) +
          BinaryMultiplication.work first.denominator second.denominator + 4

theorem rawAddWork_bound (first second : SignedWord) :
    rawAddWork first second ≤ 500 * (pairWidth first second + 1) ^ 2 := by
  let W := pairWidth first second
  have hw := operand_widths first second
  have hL := BinarySignedMagnitude.multiplyWork_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hR := BinarySignedMagnitude.multiplyWork_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hD := unsignedMultiplyWork_bound first.denominator second.denominator W hw.2.1 hw.2.2.2
  have hA := BinarySignedMagnitude.addWork_bound
    (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
    (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first))
  have hLL := BinaryMultiplication.multiply_length first.numerator second.denominator
  have hRL := BinaryMultiplication.multiply_length second.numerator first.denominator
  change (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)).bits.length ≤ _ at hLL
  change (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)).bits.length ≤ _ at hRL
  have hMax : max (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)).bits.length
      (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)).bits.length ≤ 3 * W := by
    dsimp only [W]
    omega
  have hAB := hA.trans (Nat.mul_le_mul_left 51 (Nat.add_le_add_right hMax 1))
  unfold rawAddWork
  change _ ≤ 500 * (W + 1) ^ 2
  nlinarith

def rawMultiplyWork (first second : SignedWord) : ℕ :=
  BinarySignedMagnitude.multiplyWork (numeratorWord first) (numeratorWord second) +
    BinaryMultiplication.work first.denominator second.denominator + 3

theorem rawMultiplyWork_bound (first second : SignedWord) :
    rawMultiplyWork first second ≤ 210 * (pairWidth first second + 1) ^ 2 := by
  have hw := operand_widths first second
  have hn := BinarySignedMagnitude.multiplyWork_bound (numeratorWord first) (numeratorWord second)
    (pairWidth first second) hw.1 hw.2.2.1
  have hd := unsignedMultiplyWork_bound first.denominator second.denominator
    (pairWidth first second) hw.2.1 hw.2.2.2
  unfold rawMultiplyWork
  nlinarith

def rawDivideWork (first second : SignedWord) : ℕ :=
  BinaryMultiplication.work first.numerator second.denominator +
    BinaryMultiplication.work first.denominator second.numerator + 4

theorem rawDivideWork_bound (first second : SignedWord) :
    rawDivideWork first second ≤ 210 * (pairWidth first second + 1) ^ 2 := by
  have hw := operand_widths first second
  have hn := unsignedMultiplyWork_bound first.numerator second.denominator
    (pairWidth first second) hw.1 hw.2.2.2
  have hd := unsignedMultiplyWork_bound first.denominator second.numerator
    (pairWidth first second) hw.2.1 hw.2.2.1
  unfold rawDivideWork
  nlinarith

def addWithWork (first second : SignedWord) : SignedWord × ℕ :=
  let result := normalizeWithWork (rawAdd first second)
  (result.1, rawAddWork first second + result.2)

def multiplyWithWork (first second : SignedWord) : SignedWord × ℕ :=
  let result := normalizeWithWork (rawMultiply first second)
  (result.1, rawMultiplyWork first second + result.2)

def divideWithWork (first second : SignedWord) : SignedWord × ℕ :=
  let result := normalizeWithWork (rawDivide first second)
  (result.1, rawDivideWork first second + result.2)

theorem addWithWork_state (first second : SignedWord) : (addWithWork first second).1 = add first second := rfl
theorem multiplyWithWork_state (first second : SignedWord) : (multiplyWithWork first second).1 = multiply first second := rfl
theorem divideWithWork_state (first second : SignedWord) : (divideWithWork first second).1 = divide first second := rfl

theorem addWithWork_bound (first second : SignedWord) :
    (addWithWork first second).2 ≤ 11000 * (pairWidth first second + 1) ^ 3 := by
  have hRaw := rawAddWork_bound first second
  have hNorm := normalizeWithWork_bound (rawAdd first second)
  have hWidth := rawAdd_width first second
  have hW : width (rawAdd first second) + 1 ≤ 4 * (pairWidth first second + 1) := by omega
  have hPow := Nat.pow_le_pow_left hW 3
  have hPrice := hNorm.trans (Nat.mul_le_mul_left 150 hPow)
  unfold addWithWork
  dsimp only
  nlinarith

theorem multiplyWithWork_bound (first second : SignedWord) :
    (multiplyWithWork first second).2 ≤ 11000 * (pairWidth first second + 1) ^ 3 := by
  have hRaw := rawMultiplyWork_bound first second
  have hNorm := normalizeWithWork_bound (rawMultiply first second)
  have hWidth := rawMultiply_width first second
  have hW : width (rawMultiply first second) + 1 ≤ 4 * (pairWidth first second + 1) := by omega
  have hPow := Nat.pow_le_pow_left hW 3
  have hPrice := hNorm.trans (Nat.mul_le_mul_left 150 hPow)
  unfold multiplyWithWork
  dsimp only
  nlinarith

theorem divideWithWork_bound (first second : SignedWord) :
    (divideWithWork first second).2 ≤ 11000 * (pairWidth first second + 1) ^ 3 := by
  have hRaw := rawDivideWork_bound first second
  have hNorm := normalizeWithWork_bound (rawDivide first second)
  have hWidth := rawDivide_width first second
  have hW : width (rawDivide first second) + 1 ≤ 4 * (pairWidth first second + 1) := by omega
  have hPow := Nat.pow_le_pow_left hW 3
  have hPrice := hNorm.trans (Nat.mul_le_mul_left 150 hPow)
  unfold divideWithWork
  dsimp only
  nlinarith

def subtractWithWork (first second : SignedWord) : SignedWord × ℕ :=
  let result := addWithWork first (negate second)
  (result.1, result.2 + 1)

theorem subtractWithWork_state (first second : SignedWord) : (subtractWithWork first second).1 = subtract first second := rfl

theorem subtract_width (first second : SignedWord) : width (subtract first second) ≤ 3 * pairWidth first second + 1 :=
  add_width first (negate second)

theorem subtractWithWork_bound (first second : SignedWord) :
    (subtractWithWork first second).2 ≤ 11001 * (pairWidth first second + 1) ^ 3 := by
  have h := addWithWork_bound first (negate second)
  change (addWithWork first (negate second)).2 + 1 ≤ _
  change (addWithWork first (negate second)).2 ≤ 11000 * (pairWidth first second + 1) ^ 3 at h
  have hp : 1 ≤ (pairWidth first second + 1) ^ 3 := one_le_pow₀ (by omega)
  nlinarith

def signedNonpositive (word : BinarySignedMagnitude.Word) : Bool :=
  word.negative || !BinaryEuclideanGCD.nonzero word.bits

theorem signedNonpositive_iff (word : BinarySignedMagnitude.Word) :
    signedNonpositive word = true ↔ BinarySignedMagnitude.value word ≤ 0 := by
  cases word with
  | mk negative bits =>
      cases negative
      · simp only [signedNonpositive, Bool.false_or, BinarySignedMagnitude.value,
          BinarySignedMagnitude.signedValue, Bool.false_eq_true, ite_false]
        have hz := BinaryEuclideanGCD.nonzero_false_iff bits
        cases he : BinaryEuclideanGCD.nonzero bits
        · have hn := hz.mp he
          simp only [Bool.not_false, true_iff]
          rw [hn]
          simp
        · have hn : BinaryBigEndian.littleValue bits ≠ 0 := by
            intro hn
            have hf := hz.mpr hn
            rw [he] at hf
            cases hf
          simp only [Bool.not_true, Bool.false_eq_true, false_iff]
          omega
      · simp [signedNonpositive, BinarySignedMagnitude.value, BinarySignedMagnitude.signedValue]

def lessEqual (first second : SignedWord) : Bool :=
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  signedNonpositive (BinarySignedMagnitude.subtract left right)

theorem lessEqual_iff (first second : SignedWord)
    (hA : 0 < BinaryBigEndian.littleValue first.denominator)
    (hB : 0 < BinaryBigEndian.littleValue second.denominator) :
    lessEqual first second = true ↔ value first ≤ value second := by
  rw [lessEqual, signedNonpositive_iff, BinarySignedMagnitude.subtract_value,
    BinarySignedMagnitude.multiply_value, BinarySignedMagnitude.multiply_value,
    denominatorWord_value, denominatorWord_value, value_via_integer, value_via_integer]
  have ha : (0 : ℚ) < BinaryBigEndian.littleValue first.denominator := by exact_mod_cast hA
  have hb : (0 : ℚ) < BinaryBigEndian.littleValue second.denominator := by exact_mod_cast hB
  rw [div_le_div_iff₀ ha hb]
  constructor
  · intro h
    have he : BinarySignedMagnitude.value (numeratorWord first) * (BinaryBigEndian.littleValue second.denominator : ℤ) ≤
        BinarySignedMagnitude.value (numeratorWord second) * (BinaryBigEndian.littleValue first.denominator : ℤ) := by omega
    exact_mod_cast he
  · intro h
    have he : BinarySignedMagnitude.value (numeratorWord first) * (BinaryBigEndian.littleValue second.denominator : ℤ) ≤
        BinarySignedMagnitude.value (numeratorWord second) * (BinaryBigEndian.littleValue first.denominator : ℤ) := by exact_mod_cast h
    omega

def lessEqualWork (first second : SignedWord) : ℕ :=
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  BinarySignedMagnitude.multiplyWork (numeratorWord first) (denominatorWord second) +
    BinarySignedMagnitude.multiplyWork (numeratorWord second) (denominatorWord first) +
      BinarySignedMagnitude.addWork left (BinarySignedMagnitude.negate right) +
        3 * ((BinarySignedMagnitude.subtract left right).bits.length + 1) + 5

theorem lessEqualWork_bound (first second : SignedWord) :
    lessEqualWork first second ≤ 500 * (pairWidth first second + 1) ^ 2 := by
  let W := pairWidth first second
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  have hw := operand_widths first second
  have hL := BinarySignedMagnitude.multiplyWork_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hR := BinarySignedMagnitude.multiplyWork_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hLL := BinaryMultiplication.multiply_length first.numerator second.denominator
  have hRL := BinaryMultiplication.multiply_length second.numerator first.denominator
  have hMax : max left.bits.length right.bits.length ≤ 3 * W := by
    change max (BinaryMultiplication.multiply first.numerator second.denominator).length
      (BinaryMultiplication.multiply second.numerator first.denominator).length ≤ 3 * W
    dsimp only [W]
    omega
  have hAdd := BinarySignedMagnitude.addWork_bound left (BinarySignedMagnitude.negate right)
  change BinarySignedMagnitude.addWork left (BinarySignedMagnitude.negate right) ≤ 51 * (max left.bits.length right.bits.length + 1) at hAdd
  have hAddBound := hAdd.trans (Nat.mul_le_mul_left 51 (Nat.add_le_add_right hMax 1))
  have hLen := BinarySignedMagnitude.add_length left (BinarySignedMagnitude.negate right)
  change (BinarySignedMagnitude.subtract left right).bits.length ≤ max left.bits.length right.bits.length + 1 at hLen
  unfold lessEqualWork
  change _ ≤ 500 * (W + 1) ^ 2
  nlinarith

-- This conservative profile accommodates the actual cubic normalization.
-- Its width argument includes one administrative digit. It does not assert
-- the former quadratic/fast Rat envelopes or compiler-level instruction time.
def booleanCubic : RationalCostModel where
  rat := fun w => 11001 * w ^ 3 + w
  monotone := by
    intro a b h
    have hp := Nat.pow_le_pow_left h 3
    change 11001 * a ^ 3 + a ≤ 11001 * b ^ 3 + b
    omega
  word_le := by intro w; omega
  superadditive := by
    intro a b
    have hab : 0 ≤ a * b := Nat.zero_le _
    nlinarith

theorem addWithWork_booleanCubic (first second : SignedWord) :
    (addWithWork first second).2 ≤ booleanCubic.rat (pairWidth first second + 1) := by
  have h := addWithWork_bound first second
  change _ ≤ 11001 * (pairWidth first second + 1) ^ 3 + (pairWidth first second + 1)
  omega

theorem subtractWithWork_booleanCubic (first second : SignedWord) :
    (subtractWithWork first second).2 ≤ booleanCubic.rat (pairWidth first second + 1) :=
  (subtractWithWork_bound first second).trans (Nat.le_add_right _ _)

theorem multiplyWithWork_booleanCubic (first second : SignedWord) :
    (multiplyWithWork first second).2 ≤ booleanCubic.rat (pairWidth first second + 1) := by
  have h := multiplyWithWork_bound first second
  change _ ≤ 11001 * (pairWidth first second + 1) ^ 3 + (pairWidth first second + 1)
  omega

theorem divideWithWork_booleanCubic (first second : SignedWord) :
    (divideWithWork first second).2 ≤ booleanCubic.rat (pairWidth first second + 1) := by
  have h := divideWithWork_bound first second
  change _ ≤ 11001 * (pairWidth first second + 1) ^ 3 + (pairWidth first second + 1)
  omega

end Blotto.BinaryRationalArithmetic
