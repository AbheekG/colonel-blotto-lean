import Blotto.BinaryLongDivision

/-! Euclidean GCD on Boolean words uses the verified long-division remainder.
Two Euclidean steps halve the positive second value, giving a certified
2*(input width+1) fuel schedule. Numeric gcd/div/mod are proof specifications;
runtime tests and arithmetic act on Boolean lists, including leading zeros. -/

namespace Blotto.BinaryEuclideanGCD

def nonzero (bits : List Bool) : Bool := bits.any id

theorem nonzero_false_iff (bits : List Bool) : nonzero bits = false ↔ BinaryBigEndian.littleValue bits = 0 := by
  induction bits with
  | nil => simp [nonzero, BinaryBigEndian.littleValue]
  | cons bit rest ih =>
      change (bit || nonzero rest) = false ↔ 2 * BinaryBigEndian.littleValue rest + (if bit then 1 else 0) = 0
      cases bit <;> simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
      · rw [ih]
        omega
      · simp

theorem nonzero_true_iff (bits : List Bool) : nonzero bits = true ↔ 0 < BinaryBigEndian.littleValue bits := by
  have h := nonzero_false_iff bits
  constructor
  · intro ht
    by_contra hn
    have hz : BinaryBigEndian.littleValue bits = 0 := by omega
    have hf := h.mpr hz
    rw [ht] at hf
    cases hf
  · intro hp
    cases he : nonzero bits
    · have hz := h.mp he
      omega
    · rfl

def loop : ℕ → List Bool → List Bool → List Bool
  | 0, first, _second => first
  | fuel + 1, first, second =>
      if nonzero second then loop fuel second (BinaryLongDivision.divide first second).2 else first

theorem euclidean_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

theorem two_step_halving (a b : ℕ) (hb : 0 < b) (hr : 0 < a % b) :
    2 * (b % (a % b)) < b := by
  let r := a % b
  change 2 * (b % r) < b
  have hrb : r < b := Nat.mod_lt a hb
  have hs : b % r < r := Nat.mod_lt b hr
  by_cases hsmall : 2 * r ≤ b
  · omega
  · have hq : 0 < b / r := by
      by_contra hn
      have hz : b / r = 0 := Nat.eq_zero_of_not_pos hn
      have he := Nat.mod_add_div b r
      rw [hz, Nat.mul_zero, Nat.add_zero] at he
      omega
    have he := Nat.mod_add_div b r
    have hmul : r ≤ r * (b / r) := Nat.le_mul_of_pos_right r hq
    omega

theorem loop_correct (width : ℕ) (first second : List Bool)
    (hSecond : BinaryBigEndian.littleValue second < 2 ^ width) :
    BinaryBigEndian.littleValue (loop (2 * width) first second) =
      Nat.gcd (BinaryBigEndian.littleValue first) (BinaryBigEndian.littleValue second) := by
  induction width generalizing first second with
  | zero =>
      have hz : BinaryBigEndian.littleValue second = 0 := by simpa using hSecond
      simp [loop, hz]
  | succ width ih =>
      have hFuel : 2 * (width + 1) = (2 * width + 1) + 1 := by omega
      rw [hFuel, loop]
      by_cases hb : nonzero second = true
      · rw [ite_eq_left hb]
        have hb0 := (nonzero_true_iff second).mp hb
        let remainder := (BinaryLongDivision.divide first second).2
        have hrem : BinaryBigEndian.littleValue remainder =
            BinaryBigEndian.littleValue first % BinaryBigEndian.littleValue second :=
          (BinaryLongDivision.divide_div_mod first second hb0).2
        rw [loop]
        by_cases hr : nonzero remainder = true
        · rw [ite_eq_left hr]
          have hr0 := (nonzero_true_iff remainder).mp hr
          let next := (BinaryLongDivision.divide second remainder).2
          have hnext : BinaryBigEndian.littleValue next =
              BinaryBigEndian.littleValue second % BinaryBigEndian.littleValue remainder :=
            (BinaryLongDivision.divide_div_mod second remainder hr0).2
          have hHalf := two_step_halving (BinaryBigEndian.littleValue first)
            (BinaryBigEndian.littleValue second) hb0 (by rw [← hrem]; exact hr0)
          have hBound : BinaryBigEndian.littleValue next < 2 ^ width := by
            rw [hnext, hrem]
            rw [pow_succ] at hSecond
            omega
          change BinaryBigEndian.littleValue (loop (2 * width) remainder next) = _
          rw [ih remainder next hBound]
          rw [hnext, hrem]
          rw [euclidean_step (BinaryBigEndian.littleValue first), euclidean_step (BinaryBigEndian.littleValue second)]
        · rw [ite_eq_right hr]
          have hz : BinaryBigEndian.littleValue remainder = 0 := by
            apply (nonzero_false_iff remainder).mp
            cases hn : nonzero remainder <;> simp_all
          rw [euclidean_step, ← hrem, hz, Nat.gcd_zero_right]
      · rw [ite_eq_right hb]
        have hz : BinaryBigEndian.littleValue second = 0 := by
          apply (nonzero_false_iff second).mp
          cases hn : nonzero second <;> simp_all
        rw [hz, Nat.gcd_zero_right]

def width (first second : List Bool) : ℕ := max first.length second.length

def gcd (first second : List Bool) : List Bool := loop (2 * (width first second + 1)) first second

theorem gcd_value (first second : List Bool) : BinaryBigEndian.littleValue (gcd first second) =
    Nat.gcd (BinaryBigEndian.littleValue first) (BinaryBigEndian.littleValue second) := by
  apply loop_correct (width first second + 1)
  have h := BinaryBorrowWord.littleValue_bounds second
  have hp : 2 ^ second.length ≤ 2 ^ (width first second + 1) := by
    apply Nat.pow_le_pow_right (by decide)
    unfold width
    omega
  exact h.trans_le hp

theorem loop_length_bound (fuel : ℕ) (first second : List Bool) (W : ℕ)
    (hFirst : first.length ≤ W) (hSecond : second.length ≤ W) :
    (loop fuel first second).length ≤ W := by
  induction fuel generalizing first second with
  | zero => exact hFirst
  | succ fuel ih =>
      rw [loop]
      split
      · exact ih second (BinaryLongDivision.divide first second).2 hSecond
          ((BinaryLongDivision.divide_lengths first second).2.le.trans hSecond)
      · exact hFirst

theorem gcd_length (first second : List Bool) : (gcd first second).length ≤ width first second :=
  loop_length_bound _ first second _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

def zeroScanWork (bits : List Bool) : ℕ := 3 * (bits.length + 1)

def loopWork : ℕ → List Bool → List Bool → ℕ
  | 0, _first, _second => 1
  | fuel + 1, first, second =>
      zeroScanWork second + 2 + if nonzero second then
        BinaryLongDivision.bitWork first second + loopWork fuel second (BinaryLongDivision.divide first second).2
      else 0

theorem loopWork_bound (fuel : ℕ) (first second : List Bool) (W : ℕ)
    (hFirst : first.length ≤ W) (hSecond : second.length ≤ W) :
    loopWork fuel first second ≤ 1 + fuel * (30 * (W + 1) ^ 2 + 3 * (W + 1) + 2) := by
  induction fuel generalizing first second with
  | zero => simp [loopWork]
  | succ fuel ih =>
      have hd := BinaryLongDivision.bitWork_quadratic first second
      have hdBound : BinaryLongDivision.bitWork first second ≤ 30 * (W + 1) ^ 2 := by
        have hmul := Nat.mul_le_mul (Nat.add_le_add_right hFirst 1) (Nat.add_le_add_right hSecond 1)
        calc
          _ ≤ 30 * (first.length + 1) * (second.length + 1) := hd
          _ = 30 * ((first.length + 1) * (second.length + 1)) := by ring
          _ ≤ 30 * ((W + 1) * (W + 1)) := Nat.mul_le_mul_left 30 hmul
          _ = _ := by ring
      have hTail := ih second (BinaryLongDivision.divide first second).2 hSecond
        ((BinaryLongDivision.divide_lengths first second).2.le.trans hSecond)
      unfold loopWork zeroScanWork
      split <;> nlinarith

def bitWork (first second : List Bool) : ℕ := loopWork (2 * (width first second + 1)) first second

theorem bitWork_bound (first second : List Bool) : bitWork first second ≤
    1 + 2 * (width first second + 1) *
      (30 * (width first second + 1) ^ 2 + 3 * (width first second + 1) + 2) :=
  loopWork_bound _ first second _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

def loopWithWork : ℕ → List Bool → List Bool → List Bool × ℕ
  | 0, first, _second => (first, 1)
  | fuel + 1, first, second =>
      if nonzero second then
        let division := BinaryLongDivision.divideWithWork first second
        let later := loopWithWork fuel second division.1.2
        (later.1, zeroScanWork second + 2 + (division.2 + later.2))
      else (first, zeroScanWork second + 2)

theorem loopWithWork_refines (fuel : ℕ) (first second : List Bool) :
    loopWithWork fuel first second = (loop fuel first second, loopWork fuel first second) := by
  induction fuel generalizing first second with
  | zero => rfl
  | succ fuel ih =>
      rw [loopWithWork]
      split
      · rename_i h
        rw [BinaryLongDivision.divideWithWork_refines]
        dsimp only
        rw [ih]
        simp [loop, loopWork, h]
      · rename_i h
        simp [loop, loopWork, h]

def gcdWithWork (first second : List Bool) : List Bool × ℕ :=
  let W := width first second
  let result := loopWithWork (2 * (W + 1)) first second
  -- Reading both widths and forming the linear fuel adds an explicit allowance.
  (result.1, first.length + second.length + 4 * (W + 1) + result.2)

theorem gcdWithWork_value (first second : List Bool) :
    BinaryBigEndian.littleValue (gcdWithWork first second).1 =
      Nat.gcd (BinaryBigEndian.littleValue first) (BinaryBigEndian.littleValue second) := by
  unfold gcdWithWork
  dsimp only
  rw [loopWithWork_refines]
  exact gcd_value first second

theorem gcdWithWork_length (first second : List Bool) :
    (gcdWithWork first second).1.length ≤ width first second := by
  unfold gcdWithWork
  dsimp only
  rw [loopWithWork_refines]
  exact gcd_length first second

theorem gcdWithWork_bound (first second : List Bool) :
    (gcdWithWork first second).2 ≤ 80 * (width first second + 1) ^ 3 := by
  have h := bitWork_bound first second
  have ha : first.length ≤ width first second := Nat.le_max_left _ _
  have hb : second.length ≤ width first second := Nat.le_max_right _ _
  unfold gcdWithWork
  dsimp only
  rw [loopWithWork_refines]
  change first.length + second.length + 4 * (width first second + 1) + bitWork first second ≤ _
  nlinarith

theorem gcdWithWork_contract (first second : List Bool) :
    BinaryBigEndian.littleValue (gcdWithWork first second).1 =
        Nat.gcd (BinaryBigEndian.littleValue first) (BinaryBigEndian.littleValue second) ∧
      (gcdWithWork first second).1.length ≤ width first second ∧
      (gcdWithWork first second).2 ≤ 80 * (width first second + 1) ^ 3 :=
  ⟨gcdWithWork_value first second, gcdWithWork_length first second, gcdWithWork_bound first second⟩

end Blotto.BinaryEuclideanGCD
