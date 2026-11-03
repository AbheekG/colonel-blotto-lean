import Blotto.BinaryDivisionWordStep

/-! Restoring long division scans most-significant-first dividend bits and
retains fixed-width little-endian remainder words. Quotient bits are prepended
to a little-endian accumulator. Runtime calls only Boolean/list routines;
Nat division, remainder, multiplication and values below are specifications.
The cost is an explicit abstract Boolean/cell RAM bound, not native CPU/GC time. -/

namespace Blotto.BinaryLongDivision

def loop (divisor : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], quotient, remainder => (quotient, remainder)
  | incoming :: rest, quotient, remainder =>
      let next := BinaryDivisionWord.step incoming remainder divisor
      loop divisor rest (next.1 :: quotient) next.2

theorem loop_lengths (divisor bits quotient remainder : List Bool)
    (hWidth : remainder.length = divisor.length) :
    (loop divisor bits quotient remainder).1.length = quotient.length + bits.length ∧
      (loop divisor bits quotient remainder).2.length = divisor.length := by
  induction bits generalizing quotient remainder with
  | nil => exact ⟨by simp [loop], hWidth⟩
  | cons incoming rest ih =>
      have hStep := BinaryDivisionWord.step_length incoming remainder divisor hWidth
      have h := ih ((BinaryDivisionWord.step incoming remainder divisor).1 :: quotient)
        (BinaryDivisionWord.step incoming remainder divisor).2 (hStep.trans hWidth)
      simpa only [loop, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem loop_remainder_lt (divisor bits quotient remainder : List Bool)
    (hWidth : remainder.length = divisor.length)
    (hRem : BinaryBigEndian.littleValue remainder < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue (loop divisor bits quotient remainder).2 < BinaryBigEndian.littleValue divisor := by
  induction bits generalizing quotient remainder with
  | nil => exact hRem
  | cons incoming rest ih =>
      exact ih ((BinaryDivisionWord.step incoming remainder divisor).1 :: quotient)
        (BinaryDivisionWord.step incoming remainder divisor).2
        ((BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
        (BinaryDivisionWord.step_remainder_lt incoming remainder divisor hWidth hRem)

theorem loop_balance (divisor bits quotient remainder : List Bool)
    (hWidth : remainder.length = divisor.length)
    (hRem : BinaryBigEndian.littleValue remainder < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue divisor * BinaryBigEndian.littleValue (loop divisor bits quotient remainder).1 +
      BinaryBigEndian.littleValue (loop divisor bits quotient remainder).2 =
        (BinaryBigEndian.littleValue divisor * BinaryBigEndian.littleValue quotient + BinaryBigEndian.littleValue remainder) *
          2 ^ bits.length + BinaryBigEndian.value bits := by
  induction bits generalizing quotient remainder with
  | nil => simp [loop, BinaryBigEndian.value]
  | cons incoming rest ih =>
      have hStep := BinaryDivisionWord.step_balance incoming remainder divisor hWidth hRem
      have h := ih ((BinaryDivisionWord.step incoming remainder divisor).1 :: quotient)
        (BinaryDivisionWord.step incoming remainder divisor).2
        ((BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
        (BinaryDivisionWord.step_remainder_lt incoming remainder divisor hWidth hRem)
      rw [loop, h]
      change (BinaryBigEndian.littleValue divisor *
        (2 * BinaryBigEndian.littleValue quotient + BinaryBorrowWord.digit (BinaryDivisionWord.step incoming remainder divisor).1) +
        BinaryBigEndian.littleValue (BinaryDivisionWord.step incoming remainder divisor).2) * 2 ^ rest.length +
        BinaryBigEndian.value rest = _
      have hHead : BinaryBigEndian.value (incoming :: rest) =
          BinaryBorrowWord.digit incoming * 2 ^ rest.length + BinaryBigEndian.value rest := by
        cases incoming <;> simp [BinaryBigEndian.value, BinaryBorrowWord.digit]
      rw [hHead, List.length_cons, pow_succ]
      calc
        _ = (2 * (BinaryBigEndian.littleValue divisor * BinaryBigEndian.littleValue quotient) +
            (BinaryBigEndian.littleValue divisor * BinaryBorrowWord.digit (BinaryDivisionWord.step incoming remainder divisor).1 +
              BinaryBigEndian.littleValue (BinaryDivisionWord.step incoming remainder divisor).2)) * 2 ^ rest.length +
              BinaryBigEndian.value rest := by ring
        _ = _ := by rw [← hStep]; ring

def zeroRemainder (divisor : List Bool) : List Bool := List.replicate divisor.length false

theorem zeroRemainder_length (divisor : List Bool) : (zeroRemainder divisor).length = divisor.length := by
  simp [zeroRemainder]

theorem zeroRemainder_value (divisor : List Bool) : BinaryBigEndian.littleValue (zeroRemainder divisor) = 0 := by
  have h : ∀ n, BinaryBigEndian.littleValue (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, BinaryBigEndian.littleValue, ih]
  exact h divisor.length

def divideBigEndian (dividend divisor : List Bool) : List Bool × List Bool :=
  loop divisor dividend [] (zeroRemainder divisor)

theorem divideBigEndian_lengths (dividend divisor : List Bool) :
    (divideBigEndian dividend divisor).1.length = dividend.length ∧
      (divideBigEndian dividend divisor).2.length = divisor.length := by
  simpa only [divideBigEndian, List.length_nil, Nat.zero_add] using
    loop_lengths divisor dividend [] (zeroRemainder divisor) (zeroRemainder_length divisor)

theorem divideBigEndian_remainder_lt (dividend divisor : List Bool)
    (hD : 0 < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue (divideBigEndian dividend divisor).2 < BinaryBigEndian.littleValue divisor :=
  loop_remainder_lt divisor dividend [] (zeroRemainder divisor) (zeroRemainder_length divisor)
    (by rw [zeroRemainder_value]; exact hD)

theorem divideBigEndian_balance (dividend divisor : List Bool)
    (hD : 0 < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue divisor * BinaryBigEndian.littleValue (divideBigEndian dividend divisor).1 +
      BinaryBigEndian.littleValue (divideBigEndian dividend divisor).2 = BinaryBigEndian.value dividend := by
  have h := loop_balance divisor dividend [] (zeroRemainder divisor) (zeroRemainder_length divisor)
    (by rw [zeroRemainder_value]; exact hD)
  simpa only [divideBigEndian, BinaryBigEndian.littleValue, zeroRemainder_value, Nat.mul_zero,
    Nat.zero_add, Nat.zero_mul] using h

theorem divideBigEndian_div_mod (dividend divisor : List Bool)
    (hD : 0 < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue (divideBigEndian dividend divisor).1 =
        BinaryBigEndian.value dividend / BinaryBigEndian.littleValue divisor ∧
      BinaryBigEndian.littleValue (divideBigEndian dividend divisor).2 =
        BinaryBigEndian.value dividend % BinaryBigEndian.littleValue divisor := by
  have hb := divideBigEndian_balance dividend divisor hD
  have hr := divideBigEndian_remainder_lt dividend divisor hD
  have hN : BinaryBigEndian.value dividend =
      BinaryBigEndian.littleValue divisor * BinaryBigEndian.littleValue (divideBigEndian dividend divisor).1 +
        BinaryBigEndian.littleValue (divideBigEndian dividend divisor).2 := hb.symm
  constructor
  · rw [hN, Nat.mul_add_div (Nat.zero_lt_of_lt hD), Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [hN, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

def divide (dividend divisor : List Bool) : List Bool × List Bool := divideBigEndian dividend.reverse divisor

theorem divide_div_mod (dividend divisor : List Bool) (hD : 0 < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue (divide dividend divisor).1 =
        BinaryBigEndian.littleValue dividend / BinaryBigEndian.littleValue divisor ∧
      BinaryBigEndian.littleValue (divide dividend divisor).2 =
        BinaryBigEndian.littleValue dividend % BinaryBigEndian.littleValue divisor := by
  simpa only [divide, BinaryBigEndian.value_reverse] using divideBigEndian_div_mod dividend.reverse divisor hD

-- Work follows the same digit/remainder updates. Each digit adds one input
-- read, one quotient cons, and two loop/control labels to the step allowance.
def loopWork (divisor : List Bool) : List Bool → List Bool → ℕ
  | [], _ => 1
  | incoming :: rest, remainder =>
      BinaryDivisionWord.bitWork incoming remainder divisor + 4 +
        loopWork divisor rest (BinaryDivisionWord.step incoming remainder divisor).2

theorem loopWork_bound (divisor bits remainder : List Bool) (hWidth : remainder.length = divisor.length) :
    loopWork divisor bits remainder ≤ 1 + bits.length * (17 * divisor.length + 24) := by
  induction bits generalizing remainder with
  | nil => simp [loopWork]
  | cons incoming rest ih =>
      have hStep := BinaryDivisionWord.bitWork_bound incoming remainder divisor hWidth
      rw [hWidth] at hStep
      have hRest := ih (BinaryDivisionWord.step incoming remainder divisor).2
        ((BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
      simp only [loopWork, List.length_cons]
      exact (Nat.add_le_add_right (Nat.add_le_add_right hStep 4) _).trans
        ((Nat.add_le_add_left hRest _).trans_eq (by ring))

def loopWithWork (divisor : List Bool) :
    List Bool → List Bool → List Bool → (List Bool × List Bool) × ℕ
  | [], quotient, remainder => ((quotient, remainder), 1)
  | incoming :: rest, quotient, remainder =>
      let next := BinaryDivisionWord.step incoming remainder divisor
      let later := loopWithWork divisor rest (next.1 :: quotient) next.2
      (later.1, BinaryDivisionWord.bitWork incoming remainder divisor + 4 + later.2)

theorem loopWithWork_refines (divisor bits quotient remainder : List Bool) :
    loopWithWork divisor bits quotient remainder =
      (loop divisor bits quotient remainder, loopWork divisor bits remainder) := by
  induction bits generalizing quotient remainder with
  | nil => rfl
  | cons incoming rest ih =>
      rw [loopWithWork, ih]
      rfl

def bitWork (dividend divisor : List Bool) : ℕ :=
  2 * dividend.length + 2 * divisor.length + loopWork divisor dividend.reverse (zeroRemainder divisor) + 2

def divideWithWork (dividend divisor : List Bool) : (List Bool × List Bool) × ℕ :=
  let result := loopWithWork divisor dividend.reverse [] (zeroRemainder divisor)
  (result.1, 2 * dividend.length + 2 * divisor.length + result.2 + 2)

theorem divideWithWork_refines (dividend divisor : List Bool) :
    divideWithWork dividend divisor = (divide dividend divisor, bitWork dividend divisor) := by
  rw [divideWithWork, loopWithWork_refines]
  rfl

theorem bitWork_bound (dividend divisor : List Bool) : bitWork dividend divisor ≤
    2 * dividend.length + 2 * divisor.length + 3 + dividend.length * (17 * divisor.length + 24) := by
  have h := loopWork_bound divisor dividend.reverse (zeroRemainder divisor) (zeroRemainder_length divisor)
  rw [List.length_reverse] at h
  unfold bitWork
  omega

theorem divide_lengths (dividend divisor : List Bool) :
    (divide dividend divisor).1.length = dividend.length ∧
      (divide dividend divisor).2.length = divisor.length := by
  simpa only [divide, List.length_reverse] using divideBigEndian_lengths dividend.reverse divisor

theorem bitWork_quadratic (dividend divisor : List Bool) :
    bitWork dividend divisor ≤ 30 * (dividend.length + 1) * (divisor.length + 1) := by
  have h := bitWork_bound dividend divisor
  nlinarith

theorem divideWithWork_contract (dividend divisor : List Bool)
    (hD : 0 < BinaryBigEndian.littleValue divisor) :
    let result := divideWithWork dividend divisor
    BinaryBigEndian.littleValue result.1.1 =
        BinaryBigEndian.littleValue dividend / BinaryBigEndian.littleValue divisor ∧
      BinaryBigEndian.littleValue result.1.2 =
        BinaryBigEndian.littleValue dividend % BinaryBigEndian.littleValue divisor ∧
      result.1.1.length = dividend.length ∧ result.1.2.length = divisor.length ∧
      result.2 ≤ 30 * (dividend.length + 1) * (divisor.length + 1) := by
  rw [divideWithWork_refines]
  exact ⟨(divide_div_mod dividend divisor hD).1, (divide_div_mod dividend divisor hD).2,
    (divide_lengths dividend divisor).1, (divide_lengths dividend divisor).2, bitWork_quadratic dividend divisor⟩

end Blotto.BinaryLongDivision
