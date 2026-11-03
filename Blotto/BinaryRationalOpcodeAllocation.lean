import Blotto.BinarySignedAllocation
import Blotto.BinaryRationalOpcode

/-! Allocation and retained Boolean buffers for every native rational opcode.
Observers follow the actual raw cross products and signed branches, then the
verified GCD/two-division normalizer and reverse/drop/reverse canonical trim.
Storage conservatively retains all primitive frames and buffers until return;
this is an abstract list-cell model, separate from cubic work, fast arithmetic,
and physical allocator/GC behavior. -/

namespace Blotto.BinaryRationalOpcodeAllocation
open BinaryRationalNormalization BinaryRationalArithmetic

def payload (word : SignedWord) : ℕ := 1 + word.numerator.length + word.denominator.length

def rawAddWithAllocation (first second : SignedWord) : SignedWord × ℕ :=
  let left := BinarySignedAllocation.multiplyWithAllocation (numeratorWord first) (denominatorWord second)
  let right := BinarySignedAllocation.multiplyWithAllocation (numeratorWord second) (denominatorWord first)
  let numerator := BinarySignedAllocation.addWithAllocation left.1 right.1
  let denominator := BinaryArithmeticAllocation.multiplyWithAllocation first.denominator second.denominator
  (⟨numerator.1.negative, numerator.1.bits, denominator.1⟩,
    left.2 + right.2 + numerator.2 + denominator.2 + 4)

theorem rawAddWithAllocation_state (first second : SignedWord) :
    (rawAddWithAllocation first second).1 = rawAdd first second := by
  unfold rawAddWithAllocation rawAdd
  dsimp only
  rw [BinarySignedAllocation.multiplyWithAllocation_state,
    BinarySignedAllocation.multiplyWithAllocation_state, BinarySignedAllocation.addWithAllocation_state,
    BinaryArithmeticAllocation.multiplyWithAllocation_refines]

def rawMultiplyWithAllocation (first second : SignedWord) : SignedWord × ℕ :=
  let numerator := BinarySignedAllocation.multiplyWithAllocation (numeratorWord first) (numeratorWord second)
  let denominator := BinaryArithmeticAllocation.multiplyWithAllocation first.denominator second.denominator
  (⟨numerator.1.negative, numerator.1.bits, denominator.1⟩, numerator.2 + denominator.2 + 3)

theorem rawMultiplyWithAllocation_state (first second : SignedWord) :
    (rawMultiplyWithAllocation first second).1 = rawMultiply first second := by
  unfold rawMultiplyWithAllocation rawMultiply
  dsimp only
  rw [BinarySignedAllocation.multiplyWithAllocation_state, BinaryArithmeticAllocation.multiplyWithAllocation_refines]

def rawDivideWithAllocation (first second : SignedWord) : SignedWord × ℕ :=
  let numerator := BinaryArithmeticAllocation.multiplyWithAllocation first.numerator second.denominator
  let denominator := BinaryArithmeticAllocation.multiplyWithAllocation first.denominator second.numerator
  (⟨Bool.xor first.negative second.negative, numerator.1, denominator.1⟩, numerator.2 + denominator.2 + 4)

theorem rawDivideWithAllocation_state (first second : SignedWord) :
    (rawDivideWithAllocation first second).1 = rawDivide first second := by
  unfold rawDivideWithAllocation rawDivide
  rw [BinaryArithmeticAllocation.multiplyWithAllocation_refines, BinaryArithmeticAllocation.multiplyWithAllocation_refines]

def lessEqualWithAllocation (first second : SignedWord) : Bool × ℕ :=
  let left := BinarySignedAllocation.multiplyWithAllocation (numeratorWord first) (denominatorWord second)
  let right := BinarySignedAllocation.multiplyWithAllocation (numeratorWord second) (denominatorWord first)
  let difference := BinarySignedAllocation.subtractWithAllocation left.1 right.1
  let scan := BinaryNormalizationAllocation.scanWithFrames difference.1.bits
  (difference.1.negative || !scan.1, left.2 + right.2 + difference.2 + scan.2 + 5)

theorem lessEqualWithAllocation_state (first second : SignedWord) :
    (lessEqualWithAllocation first second).1 = lessEqual first second := by
  unfold lessEqualWithAllocation lessEqual signedNonpositive
  dsimp only
  rw [BinarySignedAllocation.multiplyWithAllocation_state,
    BinarySignedAllocation.multiplyWithAllocation_state, BinarySignedAllocation.subtractWithAllocation_state,
    BinaryNormalizationAllocation.scanWithFrames_state]

def crossStorage (first second : SignedWord) : ℕ :=
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  payload first + payload second + left.bits.length + right.bits.length + 6 +
    BinarySignedAllocation.multiplyStorage (numeratorWord first) (denominatorWord second) +
    BinarySignedAllocation.multiplyStorage (numeratorWord second) (denominatorWord first) +
    BinarySignedAllocation.addStorage left right

def rawAddStorage (first second : SignedWord) : ℕ :=
  crossStorage first second + payload (rawAdd first second) +
    BinaryArithmeticAllocation.multiplyStorage first.denominator second.denominator +
    (rawAddWithAllocation first second).2

def rawMultiplyStorage (first second : SignedWord) : ℕ :=
  payload first + payload second + payload (rawMultiply first second) + 5 +
    BinarySignedAllocation.multiplyStorage (numeratorWord first) (numeratorWord second) +
    BinaryArithmeticAllocation.multiplyStorage first.denominator second.denominator +
    (rawMultiplyWithAllocation first second).2

def rawDivideStorage (first second : SignedWord) : ℕ :=
  payload first + payload second + payload (rawDivide first second) + 5 +
    BinaryArithmeticAllocation.multiplyStorage first.numerator second.denominator +
    BinaryArithmeticAllocation.multiplyStorage first.denominator second.numerator +
    (rawDivideWithAllocation first second).2

def lessEqualStorage (first second : SignedWord) : ℕ :=
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  let difference := BinarySignedMagnitude.subtract left right
  payload first + payload second + left.bits.length + right.bits.length + difference.bits.length + 8 +
    BinarySignedAllocation.multiplyStorage (numeratorWord first) (denominatorWord second) +
    BinarySignedAllocation.multiplyStorage (numeratorWord second) (denominatorWord first) +
    BinarySignedAllocation.addStorage left (BinarySignedMagnitude.negate right) +
    (BinaryNormalizationAllocation.scanWithFrames difference.bits).2 +
    (lessEqualWithAllocation first second).2

theorem payload_bound (word : SignedWord) (W : ℕ) (h : width word ≤ W) : payload word ≤ 1 + 2 * W := by
  unfold payload width at *
  omega

theorem multiplyAllocated_bound (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    (BinaryArithmeticAllocation.multiplyWithAllocation a b).2 ≤ 25 * (W + 1) ^ 2 := by
  have h := (BinaryArithmeticAllocation.multiplyWithAllocation_contract a b W ha hb).2.1
  nlinarith

theorem cross_lengths (first second : SignedWord) :
    (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)).bits.length ≤ 3 * pairWidth first second ∧
    (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)).bits.length ≤ 3 * pairWidth first second := by
  have hw := operand_widths first second
  have hl := BinarySignedMagnitude.multiply_length (numeratorWord first) (denominatorWord second)
  have hr := BinarySignedMagnitude.multiply_length (numeratorWord second) (denominatorWord first)
  change _ ≤ 2 * first.numerator.length + second.denominator.length at hl
  change _ ≤ 2 * second.numerator.length + first.denominator.length at hr
  omega

theorem rawAddWithAllocation_bound (first second : SignedWord) :
    (rawAddWithAllocation first second).2 ≤ 150 * (pairWidth first second + 1) ^ 2 := by
  let W := pairWidth first second
  have hw := operand_widths first second
  have hl := BinarySignedAllocation.multiplyWithAllocation_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hr := BinarySignedAllocation.multiplyWithAllocation_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hd := multiplyAllocated_bound first.denominator second.denominator W hw.2.1 hw.2.2.2
  have hc := cross_lengths first second
  have ha := BinarySignedAllocation.addWithAllocation_bound
    (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
    (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)) (3 * W) hc.1 hc.2
  unfold rawAddWithAllocation
  dsimp only
  rw [BinarySignedAllocation.multiplyWithAllocation_state, BinarySignedAllocation.multiplyWithAllocation_state]
  change _ ≤ 150 * (W + 1) ^ 2
  nlinarith

theorem rawMultiplyWithAllocation_bound (first second : SignedWord) :
    (rawMultiplyWithAllocation first second).2 ≤ 100 * (pairWidth first second + 1) ^ 2 := by
  have hw := operand_widths first second
  have hn := BinarySignedAllocation.multiplyWithAllocation_bound (numeratorWord first) (numeratorWord second) _ hw.1 hw.2.2.1
  have hd := multiplyAllocated_bound first.denominator second.denominator _ hw.2.1 hw.2.2.2
  unfold rawMultiplyWithAllocation
  dsimp only
  nlinarith

theorem rawDivideWithAllocation_bound (first second : SignedWord) :
    (rawDivideWithAllocation first second).2 ≤ 100 * (pairWidth first second + 1) ^ 2 := by
  have hw := operand_widths first second
  have hn := multiplyAllocated_bound first.numerator second.denominator _ hw.1 hw.2.2.2
  have hd := multiplyAllocated_bound first.denominator second.numerator _ hw.2.1 hw.2.2.1
  unfold rawDivideWithAllocation
  dsimp only
  nlinarith

theorem lessEqualWithAllocation_bound (first second : SignedWord) :
    (lessEqualWithAllocation first second).2 ≤ 150 * (pairWidth first second + 1) ^ 2 := by
  let W := pairWidth first second
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  have hw := operand_widths first second
  have hl := BinarySignedAllocation.multiplyWithAllocation_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hr := BinarySignedAllocation.multiplyWithAllocation_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hc := cross_lengths first second
  have ha := BinarySignedAllocation.addWithAllocation_bound left (BinarySignedMagnitude.negate right) (3 * W) hc.1 hc.2
  have hs := BinaryNormalizationAllocation.scanWithFrames_bound (BinarySignedMagnitude.subtract left right).bits
  have hlen := BinarySignedMagnitude.add_length left (BinarySignedMagnitude.negate right)
  have hm : max left.bits.length right.bits.length ≤ 3 * W := max_le hc.1 hc.2
  change (BinarySignedMagnitude.subtract left right).bits.length ≤ max left.bits.length right.bits.length + 1 at hlen
  unfold lessEqualWithAllocation
  dsimp only
  rw [BinarySignedAllocation.multiplyWithAllocation_state, BinarySignedAllocation.multiplyWithAllocation_state,
    BinarySignedAllocation.subtractWithAllocation_state]
  change (BinarySignedAllocation.multiplyWithAllocation (numeratorWord first) (denominatorWord second)).2 +
    (BinarySignedAllocation.multiplyWithAllocation (numeratorWord second) (denominatorWord first)).2 +
    (BinarySignedAllocation.subtractWithAllocation left right).2 +
    (BinaryNormalizationAllocation.scanWithFrames (BinarySignedMagnitude.subtract left right).bits).2 + 5 ≤ 150 * (W + 1) ^ 2
  unfold BinarySignedAllocation.subtractWithAllocation
  dsimp only
  nlinarith

theorem crossStorage_bound (first second : SignedWord) :
    crossStorage first second ≤ 1500 * (pairWidth first second + 1) ^ 3 := by
  let W := pairWidth first second
  have hw := operand_widths first second
  have hpA := payload_bound first W (Nat.le_max_left _ _)
  have hpB := payload_bound second W (Nat.le_max_right _ _)
  have hl := BinarySignedAllocation.multiplyStorage_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hr := BinarySignedAllocation.multiplyStorage_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hc := cross_lengths first second
  have ha := BinarySignedAllocation.addStorage_bound
    (BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second))
    (BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)) (3 * W) hc.1 hc.2
  have hPower : (3 * W + 1) ^ 2 ≤ 9 * (W + 1) ^ 2 := by nlinarith
  have ha' := ha.trans (Nat.mul_le_mul_left 50 hPower)
  have hp : W + 1 ≤ (W + 1) ^ 3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 1) (by omega : 1 ≤ 3))
  have hpp : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold crossStorage
  dsimp only
  change _ ≤ 1500 * (W + 1) ^ 3
  nlinarith

theorem rawAddStorage_bound (first second : SignedWord) :
    rawAddStorage first second ≤ 2500 * (pairWidth first second + 1) ^ 3 := by
  have hw := operand_widths first second
  have hc := crossStorage_bound first second
  have hp := payload_bound (rawAdd first second) _ (rawAdd_width first second)
  have hd := BinaryArithmeticAllocation.multiplyStorage_bound first.denominator second.denominator _ hw.2.1 hw.2.2.2
  have ha := rawAddWithAllocation_bound first second
  have hpp : (pairWidth first second + 1) ^ 2 ≤ (pairWidth first second + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpl : pairWidth first second + 1 ≤ (pairWidth first second + 1) ^ 3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < pairWidth first second + 1) (by omega : 1 ≤ 3))
  unfold rawAddStorage
  nlinarith

theorem rawMultiplyStorage_bound (first second : SignedWord) :
    rawMultiplyStorage first second ≤ 1500 * (pairWidth first second + 1) ^ 3 := by
  have hw := operand_widths first second
  have hpA := payload_bound first (pairWidth first second) (Nat.le_max_left _ _)
  have hpB := payload_bound second (pairWidth first second) (Nat.le_max_right _ _)
  have hp := payload_bound (rawMultiply first second) _ (rawMultiply_width first second)
  have hn := BinarySignedAllocation.multiplyStorage_bound (numeratorWord first) (numeratorWord second) _ hw.1 hw.2.2.1
  have hd := BinaryArithmeticAllocation.multiplyStorage_bound first.denominator second.denominator _ hw.2.1 hw.2.2.2
  have ha := rawMultiplyWithAllocation_bound first second
  have hpp : (pairWidth first second + 1) ^ 2 ≤ (pairWidth first second + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpl : pairWidth first second + 1 ≤ (pairWidth first second + 1) ^ 3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < pairWidth first second + 1) (by omega : 1 ≤ 3))
  unfold rawMultiplyStorage
  nlinarith

theorem rawDivideStorage_bound (first second : SignedWord) :
    rawDivideStorage first second ≤ 1500 * (pairWidth first second + 1) ^ 3 := by
  have hw := operand_widths first second
  have hpA := payload_bound first (pairWidth first second) (Nat.le_max_left _ _)
  have hpB := payload_bound second (pairWidth first second) (Nat.le_max_right _ _)
  have hp := payload_bound (rawDivide first second) _ (rawDivide_width first second)
  have hn := BinaryArithmeticAllocation.multiplyStorage_bound first.numerator second.denominator _ hw.1 hw.2.2.2
  have hd := BinaryArithmeticAllocation.multiplyStorage_bound first.denominator second.numerator _ hw.2.1 hw.2.2.1
  have ha := rawDivideWithAllocation_bound first second
  have hpp : (pairWidth first second + 1) ^ 2 ≤ (pairWidth first second + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpl : pairWidth first second + 1 ≤ (pairWidth first second + 1) ^ 3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < pairWidth first second + 1) (by omega : 1 ≤ 3))
  unfold rawDivideStorage
  nlinarith

theorem lessEqualStorage_bound (first second : SignedWord) :
    lessEqualStorage first second ≤ 2500 * (pairWidth first second + 1) ^ 3 := by
  let W := pairWidth first second
  let left := BinarySignedMagnitude.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMagnitude.multiply (numeratorWord second) (denominatorWord first)
  have hw := operand_widths first second
  have hpA := payload_bound first W (Nat.le_max_left _ _)
  have hpB := payload_bound second W (Nat.le_max_right _ _)
  have hl := BinarySignedAllocation.multiplyStorage_bound (numeratorWord first) (denominatorWord second) W hw.1 hw.2.2.2
  have hr := BinarySignedAllocation.multiplyStorage_bound (numeratorWord second) (denominatorWord first) W hw.2.2.1 hw.2.1
  have hc := cross_lengths first second
  have ha := BinarySignedAllocation.addStorage_bound left (BinarySignedMagnitude.negate right) (3 * W) hc.1 hc.2
  have hs := BinaryNormalizationAllocation.scanWithFrames_bound (BinarySignedMagnitude.subtract left right).bits
  have hlen := BinarySignedMagnitude.add_length left (BinarySignedMagnitude.negate right)
  have hm : max left.bits.length right.bits.length ≤ 3 * W := max_le hc.1 hc.2
  change (BinarySignedMagnitude.subtract left right).bits.length ≤ max left.bits.length right.bits.length + 1 at hlen
  have halloc := lessEqualWithAllocation_bound first second
  have hPower : (3 * W + 1) ^ 2 ≤ 9 * (W + 1) ^ 2 := by nlinarith
  have ha' := ha.trans (Nat.mul_le_mul_left 50 hPower)
  have hp : W + 1 ≤ (W + 1) ^ 3 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 1) (by omega : 1 ≤ 3))
  have hpp : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold lessEqualStorage
  dsimp only
  change _ ≤ 2500 * (W + 1) ^ 3
  nlinarith

def rawApplyWithAllocation : RealArithmeticOp → SignedWord → SignedWord → SignedWord × ℕ
  | .add, first, second => rawAddWithAllocation first second
  | .sub, first, second =>
      let result := rawAddWithAllocation first (BinaryRationalArithmetic.negate second)
      (result.1, result.2 + 1)
  | .mul, first, second => rawMultiplyWithAllocation first second
  | .div, first, second =>
      let scan := BinaryNormalizationAllocation.scanWithFrames second.numerator
      if scan.1 then
        let result := rawDivideWithAllocation first second
        (result.1, result.2 + scan.2 + 2)
      else (BinaryRationalOpcode.zero, scan.2 + 3)
  | .minimum, first, second =>
      let compared := lessEqualWithAllocation first second
      (if compared.1 then first else second, compared.2 + 2)
  | .maximum, first, second =>
      let compared := lessEqualWithAllocation first second
      (if compared.1 then second else first, compared.2 + 2)

theorem rawApplyWithAllocation_state (op : RealArithmeticOp) (first second : SignedWord) :
    (rawApplyWithAllocation op first second).1 = BinaryRationalOpcode.rawApply op first second := by
  cases op
  · exact rawAddWithAllocation_state first second
  · exact rawAddWithAllocation_state first (BinaryRationalArithmetic.negate second)
  · exact rawMultiplyWithAllocation_state first second
  · simp only [rawApplyWithAllocation, BinaryRationalOpcode.rawApply,
      BinaryNormalizationAllocation.scanWithFrames_state]
    split
    · rw [rawDivideWithAllocation_state]
    · rfl
  · simp only [rawApplyWithAllocation, lessEqualWithAllocation_state]; rfl
  · simp only [rawApplyWithAllocation, lessEqualWithAllocation_state]; rfl

def rawStorage : RealArithmeticOp → SignedWord → SignedWord → ℕ
  | .add, first, second => rawAddStorage first second
  | .sub, first, second => rawAddStorage first (BinaryRationalArithmetic.negate second) + 1
  | .mul, first, second => rawMultiplyStorage first second
  | .div, first, second => payload first + payload second +
      (BinaryNormalizationAllocation.scanWithFrames second.numerator).2 + 4 +
      if BinaryEuclideanGCD.nonzero second.numerator then rawDivideStorage first second else payload BinaryRationalOpcode.zero
  | .minimum, first, second => lessEqualStorage first second + payload first + payload second + 2
  | .maximum, first, second => lessEqualStorage first second + payload first + payload second + 2

theorem rawApplyWithAllocation_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (rawApplyWithAllocation op first second).2 ≤ 200 * (pairWidth first second + 1) ^ 2 := by
  have ha := rawAddWithAllocation_bound first second
  have hs := rawAddWithAllocation_bound first (BinaryRationalArithmetic.negate second)
  change _ ≤ 150 * (pairWidth first second + 1) ^ 2 at hs
  have hm := rawMultiplyWithAllocation_bound first second
  have hd := rawDivideWithAllocation_bound first second
  have hc := lessEqualWithAllocation_bound first second
  have hz := BinaryNormalizationAllocation.scanWithFrames_bound second.numerator
  have hw := operand_widths first second
  cases op <;> simp only [rawApplyWithAllocation]
  all_goals try split
  all_goals try dsimp only
  all_goals nlinarith

theorem rawStorage_bound (op : RealArithmeticOp) (first second : SignedWord) :
    rawStorage op first second ≤ 3000 * (pairWidth first second + 1) ^ 3 := by
  have ha := rawAddStorage_bound first second
  have hs := rawAddStorage_bound first (BinaryRationalArithmetic.negate second)
  change _ ≤ 2500 * (pairWidth first second + 1) ^ 3 at hs
  have hm := rawMultiplyStorage_bound first second
  have hd := rawDivideStorage_bound first second
  have hc := lessEqualStorage_bound first second
  have hz := BinaryNormalizationAllocation.scanWithFrames_bound second.numerator
  have hw := operand_widths first second
  have hpA := payload_bound first (pairWidth first second) (Nat.le_max_left _ _)
  have hpB := payload_bound second (pairWidth first second) (Nat.le_max_right _ _)
  have hp : pairWidth first second + 1 ≤ (pairWidth first second + 1) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < pairWidth first second + 1) (by omega : 1 ≤ 3))
  cases op <;> simp only [rawStorage]
  all_goals try split
  all_goals try change _ + _ + _ + 4 + 2 ≤ _
  all_goals nlinarith

def trimBigWithFrames : List Bool → List Bool × ℕ
  | [] => ([], 1)
  | true :: rest => (true :: rest, 1)
  | false :: rest =>
      let later := trimBigWithFrames rest
      (later.1, 1 + later.2)

theorem trimBigWithFrames_state (bits : List Bool) :
    (trimBigWithFrames bits).1 = BinaryBigEndian.trim bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [trimBigWithFrames, BinaryBigEndian.trim, ih]

theorem trimBigWithFrames_bound (bits : List Bool) :
    (trimBigWithFrames bits).2 ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · simp only [trimBigWithFrames, List.length_cons]; omega
      · simp [trimBigWithFrames]

def trimWithAllocation (bits : List Bool) : List Bool × ℕ :=
  let scanned := trimBigWithFrames bits.reverse
  (scanned.1.reverse, bits.length + scanned.1.length + scanned.2 + 2)

theorem trimWithAllocation_state (bits : List Bool) :
    (trimWithAllocation bits).1 = BinaryCanonicalMagnitude.trim bits := by
  unfold trimWithAllocation BinaryCanonicalMagnitude.trim
  dsimp only
  rw [trimBigWithFrames_state]

theorem trimWithAllocation_bound (bits : List Bool) :
    (trimWithAllocation bits).2 ≤ 3 * bits.length + 3 := by
  have hs := trimBigWithFrames_bound bits.reverse
  have ht := BinaryBigEndian.trim_length bits.reverse
  rw [List.length_reverse] at hs ht
  unfold trimWithAllocation
  dsimp only
  rw [trimBigWithFrames_state]
  omega

def trimStorage (bits : List Bool) : ℕ :=
  bits.length + bits.reverse.length + (BinaryBigEndian.trim bits.reverse).length +
    (BinaryCanonicalMagnitude.trim bits).length + (trimBigWithFrames bits.reverse).2 +
      (trimWithAllocation bits).2 + 2

theorem trimStorage_bound (bits : List Bool) : trimStorage bits ≤ 8 * bits.length + 6 := by
  have hs := trimBigWithFrames_bound bits.reverse
  have ht := BinaryBigEndian.trim_length bits.reverse
  have ho := BinaryCanonicalMagnitude.trim_length bits
  have ha := trimWithAllocation_bound bits
  rw [List.length_reverse] at hs ht
  unfold trimStorage
  rw [List.length_reverse]
  omega

def canonicalizeWithAllocation (word : SignedWord) : SignedWord × ℕ :=
  let normalized := BinaryNormalizationAllocation.normalizeWithAllocation word
  let numerator := trimWithAllocation normalized.1.numerator
  let denominator := trimWithAllocation normalized.1.denominator
  (⟨normalized.1.negative, numerator.1, denominator.1⟩, normalized.2 + numerator.2 + denominator.2 + 3)

theorem canonicalizeWithAllocation_state (word : SignedWord) :
    (canonicalizeWithAllocation word).1 = BinaryRationalOpcode.canonicalize word := by
  unfold canonicalizeWithAllocation BinaryRationalOpcode.canonicalize BinaryRationalOpcode.trimWord
  dsimp only
  rw [BinaryNormalizationAllocation.normalizeWithAllocation_state, trimWithAllocation_state, trimWithAllocation_state]

theorem canonicalizeWithAllocation_bound (word : SignedWord) :
    (canonicalizeWithAllocation word).2 ≤ 250 * (width word + 2) ^ 3 := by
  have hn := BinaryNormalizationAllocation.normalizeWithAllocation_bound word
  have hnum := trimWithAllocation_bound (BinaryRationalNormalization.normalize word).numerator
  have hden := trimWithAllocation_bound (BinaryRationalNormalization.normalize word).denominator
  rw [(normalize_lengths word).1] at hnum
  rw [(normalize_lengths word).2] at hden
  have hnumL : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hdenL : word.denominator.length ≤ width word := Nat.le_max_right _ _
  have hp : width word + 2 ≤ (width word + 2) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < width word + 2) (by omega : 1 ≤ 3))
  unfold canonicalizeWithAllocation
  dsimp only
  rw [BinaryNormalizationAllocation.normalizeWithAllocation_state]
  nlinarith

def canonicalizeStorage (word : SignedWord) : ℕ :=
  payload word + payload (BinaryRationalNormalization.normalize word) +
    payload (BinaryRationalOpcode.canonicalize word) + 4 +
    BinaryNormalizationAllocation.normalizeStorage word +
    trimStorage (BinaryRationalNormalization.normalize word).numerator +
    trimStorage (BinaryRationalNormalization.normalize word).denominator

theorem canonicalizeStorage_bound (word : SignedWord) :
    canonicalizeStorage word ≤ 5000 * (width word + 2) ^ 4 := by
  have hn := BinaryNormalizationAllocation.normalizeStorage_bound word
  have hnum := trimStorage_bound (BinaryRationalNormalization.normalize word).numerator
  have hden := trimStorage_bound (BinaryRationalNormalization.normalize word).denominator
  have hlen := normalize_lengths word
  rw [hlen.1] at hnum
  rw [hlen.2] at hden
  have hp := payload_bound word (width word) le_rfl
  have hpN : payload (BinaryRationalNormalization.normalize word) = payload word := by unfold payload; rw [hlen.1, hlen.2]
  have hpC : payload (BinaryRationalOpcode.canonicalize word) ≤ payload word := by
    have ha := BinaryCanonicalMagnitude.trim_length (BinaryRationalNormalization.normalize word).numerator
    have hb := BinaryCanonicalMagnitude.trim_length (BinaryRationalNormalization.normalize word).denominator
    unfold payload BinaryRationalOpcode.canonicalize BinaryRationalOpcode.trimWord
    dsimp only
    rw [hlen.1] at ha
    rw [hlen.2] at hb
    omega
  have hPower : width word + 2 ≤ (width word + 2) ^ 4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < width word + 2) (by omega : 1 ≤ 4))
  unfold canonicalizeStorage
  rw [hpN]
  have hnumL : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hdenL : word.denominator.length ≤ width word := Nat.le_max_right _ _
  nlinarith

def applyWithAllocation (op : RealArithmeticOp) (first second : SignedWord) : SignedWord × ℕ :=
  let raw := rawApplyWithAllocation op first second
  let result := canonicalizeWithAllocation raw.1
  (result.1, raw.2 + result.2)

theorem applyWithAllocation_state (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithAllocation op first second).1 = BinaryRationalOpcode.apply op first second := by
  unfold applyWithAllocation BinaryRationalOpcode.apply
  dsimp only
  rw [rawApplyWithAllocation_state, canonicalizeWithAllocation_state]

theorem applyWithAllocation_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithAllocation op first second).2 ≤ 20000 * (pairWidth first second + 2) ^ 3 := by
  let W := pairWidth first second
  have hr := rawApplyWithAllocation_bound op first second
  have hc := canonicalizeWithAllocation_bound (BinaryRationalOpcode.rawApply op first second)
  have hw := BinaryRationalOpcode.rawApply_width op first second
  have hW : width (BinaryRationalOpcode.rawApply op first second) + 2 ≤ 4 * (W + 2) := by omega
  have hc' := hc.trans (Nat.mul_le_mul_left 250 (Nat.pow_le_pow_left hW 3))
  have hp : (W + 1) ^ 2 ≤ (W + 2) ^ 3 :=
    (Nat.pow_le_pow_left (by omega : W + 1 ≤ W + 2) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold applyWithAllocation
  dsimp only
  rw [rawApplyWithAllocation_state]
  change _ ≤ 20000 * (W + 2) ^ 3
  nlinarith

def opcodeStorage (op : RealArithmeticOp) (first second : SignedWord) : ℕ :=
  payload first + payload second + payload (BinaryRationalOpcode.rawApply op first second) +
    payload (BinaryRationalOpcode.apply op first second) + 5 + rawStorage op first second +
      canonicalizeStorage (BinaryRationalOpcode.rawApply op first second)

theorem opcodeStorage_bound (op : RealArithmeticOp) (first second : SignedWord) :
    opcodeStorage op first second ≤ 2000000 * (pairWidth first second + 2) ^ 4 := by
  let W := pairWidth first second
  let raw := BinaryRationalOpcode.rawApply op first second
  have hRaw := BinaryRationalOpcode.rawApply_width op first second
  have hRaw' : width raw ≤ 3 * W + 1 := hRaw
  have hpA := payload_bound first W (Nat.le_max_left _ _)
  have hpB := payload_bound second W (Nat.le_max_right _ _)
  have hpR := payload_bound raw (3 * W + 1) hRaw'
  have hpC : payload (BinaryRationalOpcode.apply op first second) ≤ payload raw := by
    have hn := normalize_lengths raw
    have ha := BinaryCanonicalMagnitude.trim_length (BinaryRationalNormalization.normalize raw).numerator
    have hb := BinaryCanonicalMagnitude.trim_length (BinaryRationalNormalization.normalize raw).denominator
    unfold payload BinaryRationalOpcode.apply BinaryRationalOpcode.canonicalize BinaryRationalOpcode.trimWord
    dsimp only
    change 1 + _ + _ ≤ 1 + raw.numerator.length + raw.denominator.length
    rw [hn.1] at ha
    rw [hn.2] at hb
    change 1 + (BinaryCanonicalMagnitude.trim (BinaryRationalNormalization.normalize raw).numerator).length +
      (BinaryCanonicalMagnitude.trim (BinaryRationalNormalization.normalize raw).denominator).length ≤ _
    omega
  have hs := rawStorage_bound op first second
  have hc := canonicalizeStorage_bound raw
  have hW : width raw + 2 ≤ 4 * (W + 2) := by omega
  have hPow := Nat.pow_le_pow_left hW 4
  have hc' := hc.trans (Nat.mul_le_mul_left 5000 hPow)
  have hp : W + 1 ≤ (W + 2) ^ 4 := by
    have h : W + 2 ≤ (W + 2) ^ 4 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 2) (by omega : 1 ≤ 4))
    omega
  have hpp : (W + 1) ^ 3 ≤ (W + 2) ^ 4 :=
    (Nat.pow_le_pow_left (by omega : W + 1 ≤ W + 2) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold opcodeStorage
  change _ ≤ 2000000 * (W + 2) ^ 4
  nlinarith

theorem applyWithAllocation_contract (op : RealArithmeticOp) (first second : SignedWord)
    (hA : BinaryRationalOpcode.Valid first) (hB : BinaryRationalOpcode.Valid second) :
    value (applyWithAllocation op first second).1 = op.applyRat (value first) (value second) ∧
      BinaryRationalOpcode.Valid (applyWithAllocation op first second).1 ∧
      width (applyWithAllocation op first second).1 ≤ rationalWordWidth (op.applyRat (value first) (value second)) ∧
      (applyWithAllocation op first second).2 ≤ 20000 * (pairWidth first second + 2) ^ 3 ∧
      opcodeStorage op first second ≤ 2000000 * (pairWidth first second + 2) ^ 4 := by
  rw [applyWithAllocation_state]
  exact ⟨BinaryRationalOpcode.apply_value op first second hA hB,
    BinaryRationalOpcode.apply_valid op first second hA hB,
    BinaryRationalOpcode.apply_width op first second hA hB,
    applyWithAllocation_bound op first second, opcodeStorage_bound op first second⟩

end Blotto.BinaryRationalOpcodeAllocation
