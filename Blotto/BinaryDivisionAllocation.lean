import Blotto.BinaryLongDivision
import Blotto.BinaryArithmeticAllocation

/-! Borrow subtraction and restoring division have structural list-cell
allocation and retained-buffer observers. Cons/reversal outputs, padded divisor,
shifted remainder, quotient prefix and control frames are charged explicitly.
The conservative model keeps all allocated/held buffers until return; physical
allocator headers, sharing and GC behavior are outside this abstract contract. -/

namespace Blotto.BinaryDivisionAllocation

def borrowAllocated : List Bool → List Bool → Bool → List Bool → ℕ
  | [], [], _borrow, acc => acc.length
  | a :: as, b :: bs, borrow, acc =>
      2 + borrowAllocated as bs (BinaryBorrowWord.nextBorrow a b borrow)
        (BinaryBorrowWord.difference a b borrow :: acc)
  | _, _, _borrow, acc => acc.length

def borrowWithAllocation : List Bool → List Bool → Bool → List Bool → (List Bool × Bool) × ℕ
  | [], [], borrow, acc => ((acc.reverse, borrow), acc.length)
  | a :: as, b :: bs, borrow, acc =>
      let later := borrowWithAllocation as bs (BinaryBorrowWord.nextBorrow a b borrow)
        (BinaryBorrowWord.difference a b borrow :: acc)
      (later.1, 2 + later.2)
  | _, _, borrow, acc => ((acc.reverse, borrow), acc.length)

theorem borrowWithAllocation_refines (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    borrowWithAllocation a b borrow acc = (BinaryBorrowWord.loop a b borrow acc, borrowAllocated a b borrow acc) := by
  induction a generalizing b borrow acc with
  | nil => cases b <;> rfl
  | cons bit rest ih =>
      cases b with
      | nil => rfl
      | cons other tail => rw [borrowWithAllocation, ih]; rfl

theorem borrowAllocated_bound (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    borrowAllocated a b borrow acc ≤ 3 * a.length + acc.length := by
  induction a generalizing b borrow acc with
  | nil => cases b <;> simp [borrowAllocated]
  | cons bit rest ih =>
      cases b with
      | nil => simp [borrowAllocated]
      | cons other tail =>
          have h := ih tail (BinaryBorrowWord.nextBorrow bit other borrow)
            (BinaryBorrowWord.difference bit other borrow :: acc)
          simp only [borrowAllocated, List.length_cons] at h ⊢
          omega

def borrowHeld : List Bool → List Bool → Bool → List Bool → ℕ
  | a :: as, b :: bs, borrow, acc =>
      (a :: as).length + (b :: bs).length + acc.length + 2 +
        borrowHeld as bs (BinaryBorrowWord.nextBorrow a b borrow)
          (BinaryBorrowWord.difference a b borrow :: acc)
  | a, b, _borrow, acc => a.length + b.length + acc.length + 2

theorem borrowHeld_bound (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    borrowHeld a b borrow acc ≤ (a.length + 1) * (a.length + b.length + acc.length + 2) := by
  induction a generalizing b borrow acc with
  | nil => cases b <;> simp [borrowHeld]
  | cons bit rest ih =>
      cases b with
      | nil => simp [borrowHeld]
      | cons other tail =>
          have h := ih tail (BinaryBorrowWord.nextBorrow bit other borrow)
            (BinaryBorrowWord.difference bit other borrow :: acc)
          simp only [borrowHeld, List.length_cons] at h ⊢
          nlinarith

def borrowStorage (a b : List Bool) : ℕ := borrowHeld a b false [] + borrowAllocated a b false []

theorem borrowStorage_bound (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    borrowStorage a b ≤ 6 * (W + 1) ^ 2 := by
  have hh := borrowHeld_bound a b false []
  have hc := borrowAllocated_bound a b false []
  simp only [List.length_nil, Nat.add_zero] at hh hc
  unfold borrowStorage
  nlinarith

def dropAllocated : List Bool → List Bool → ℕ
  | [], acc => acc.length
  | [_], acc => acc.length
  | _ :: next :: rest, acc => 2 + dropAllocated (next :: rest) (false :: acc)

def dropWithAllocation : List Bool → List Bool → List Bool × ℕ
  | [], acc => (acc.reverse, acc.length)
  | [_], acc => (acc.reverse, acc.length)
  | bit :: next :: rest, acc =>
      let later := dropWithAllocation (next :: rest) (bit :: acc)
      (later.1, 2 + later.2)

theorem dropAllocated_acc_length (bits first second : List Bool) (h : first.length = second.length) :
    dropAllocated bits first = dropAllocated bits second := by
  induction bits generalizing first second with
  | nil => exact h
  | cons bit rest ih =>
      cases rest with
      | nil => exact h
      | cons next tail => exact congrArg (fun n => 2 + n) (ih _ _ (congrArg Nat.succ h))

theorem dropWithAllocation_refines (bits acc : List Bool) :
    dropWithAllocation bits acc = (BinaryWordHighBit.loop bits acc, dropAllocated bits acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          rw [dropWithAllocation, ih]
          have h := dropAllocated_acc_length (next :: tail) (bit :: acc) (false :: acc) rfl
          rw [h]
          rfl

theorem dropAllocated_bound (bits acc : List Bool) : dropAllocated bits acc ≤ 3 * bits.length + acc.length := by
  induction bits generalizing acc with
  | nil => simp [dropAllocated]
  | cons bit rest ih =>
      cases rest with
      | nil => simp [dropAllocated]
      | cons next tail =>
          have h := ih (false :: acc)
          simp only [dropAllocated, List.length_cons] at h ⊢
          omega

def dropHeld : List Bool → List Bool → ℕ
  | [], acc => acc.length + 1
  | [_bit], acc => 1 + acc.length + 1
  | _bit :: next :: rest, acc =>
      (next :: rest).length + 1 + acc.length + 1 + dropHeld (next :: rest) (false :: acc)

theorem dropHeld_bound (bits acc : List Bool) :
    dropHeld bits acc ≤ (bits.length + 1) * (bits.length + acc.length + 1) := by
  induction bits generalizing acc with
  | nil => simp [dropHeld]
  | cons bit rest ih =>
      cases rest with
      | nil => simp [dropHeld]
      | cons next tail =>
          have h := ih (false :: acc)
          simp only [dropHeld, List.length_cons] at h ⊢
          nlinarith

def stepWithAllocation (incoming : Bool) (remainder divisor : List Bool) : (Bool × List Bool) × ℕ :=
  let shifted := incoming :: remainder
  let padded := divisor ++ [false]
  let difference := borrowWithAllocation shifted padded false []
  let chosen := if difference.1.2 then shifted else difference.1.1
  let dropped := dropWithAllocation chosen []
  ((!(difference.1.2), dropped.1),
    1 + (divisor.length + 1) + difference.2 + dropped.2 + 4)

theorem stepWithAllocation_state (incoming : Bool) (remainder divisor : List Bool) :
    (stepWithAllocation incoming remainder divisor).1 = BinaryDivisionWord.step incoming remainder divisor := by
  unfold stepWithAllocation
  dsimp only
  rw [borrowWithAllocation_refines]
  dsimp only
  rw [dropWithAllocation_refines]
  unfold BinaryDivisionWord.step BinaryBorrowWord.subtract BinaryWordHighBit.drop
  dsimp only
  cases (BinaryBorrowWord.loop (incoming :: remainder) (divisor ++ [false]) false []).2 <;> simp

theorem stepWithAllocation_bound (incoming : Bool) (remainder divisor : List Bool)
    (hWidth : remainder.length = divisor.length) :
    (stepWithAllocation incoming remainder divisor).2 ≤ 7 * divisor.length + 12 := by
  have hBorrow := borrowAllocated_bound (incoming :: remainder) (divisor ++ [false]) false []
  have hLength := BinaryDivisionWord.chosenResidual_length incoming remainder divisor hWidth
  have hDrop := dropAllocated_bound (BinaryDivisionWord.chosenResidual incoming remainder divisor) []
  rw [hLength] at hDrop
  simp only [List.length_nil, Nat.add_zero, List.length_cons] at hBorrow hDrop
  unfold stepWithAllocation
  dsimp only
  rw [borrowWithAllocation_refines, dropWithAllocation_refines]
  dsimp only
  change _ + dropAllocated (BinaryDivisionWord.chosenResidual incoming remainder divisor) [] + 4 ≤ _
  rw [hWidth] at hBorrow hDrop
  omega

def stepStorage (incoming : Bool) (remainder divisor : List Bool) : ℕ :=
  remainder.length + divisor.length + (incoming :: remainder).length + (divisor ++ [false]).length + 4 +
    borrowStorage (incoming :: remainder) (divisor ++ [false]) +
      -- Dropping the high bit retains the input and all prefix accumulators.
      dropHeld (BinaryDivisionWord.chosenResidual incoming remainder divisor) [] +
        (stepWithAllocation incoming remainder divisor).2

theorem stepStorage_bound (incoming : Bool) (remainder divisor : List Bool)
    (hWidth : remainder.length = divisor.length) : stepStorage incoming remainder divisor ≤ 50 * (divisor.length + 2) ^ 2 := by
  have hBorrow := borrowStorage_bound (incoming :: remainder) (divisor ++ [false]) (divisor.length + 1)
    (by simp only [List.length_cons, hWidth]; omega) (by simp)
  have hChosen := BinaryDivisionWord.chosenResidual_length incoming remainder divisor hWidth
  have hDrop := dropHeld_bound (BinaryDivisionWord.chosenResidual incoming remainder divisor) []
  rw [hChosen] at hDrop
  simp only [List.length_nil, Nat.add_zero, hWidth] at hDrop
  have hAlloc := stepWithAllocation_bound incoming remainder divisor hWidth
  unfold stepStorage
  simp only [List.length_cons, List.length_append, List.length_nil, hWidth]
  nlinarith

def divisionLoopAllocated (divisor : List Bool) : List Bool → List Bool → ℕ
  | [], _remainder => 1
  | incoming :: rest, remainder =>
      (stepWithAllocation incoming remainder divisor).2 + 2 +
        divisionLoopAllocated divisor rest (BinaryDivisionWord.step incoming remainder divisor).2

def divisionLoopWithAllocation (divisor : List Bool) :
    List Bool → List Bool → List Bool → (List Bool × List Bool) × ℕ
  | [], quotient, remainder => ((quotient, remainder), 1)
  | incoming :: rest, quotient, remainder =>
      let digit := stepWithAllocation incoming remainder divisor
      let later := divisionLoopWithAllocation divisor rest (digit.1.1 :: quotient) digit.1.2
      (later.1, digit.2 + 2 + later.2)

theorem divisionLoopWithAllocation_refines (divisor bits quotient remainder : List Bool) :
    divisionLoopWithAllocation divisor bits quotient remainder =
      (BinaryLongDivision.loop divisor bits quotient remainder, divisionLoopAllocated divisor bits remainder) := by
  induction bits generalizing quotient remainder with
  | nil => rfl
  | cons incoming rest ih =>
      rw [divisionLoopWithAllocation]
      have hState := stepWithAllocation_state incoming remainder divisor
      rw [hState, ih]
      rfl

theorem divisionLoopAllocated_bound (divisor bits remainder : List Bool)
    (hWidth : remainder.length = divisor.length) :
    divisionLoopAllocated divisor bits remainder ≤ 1 + bits.length * (7 * divisor.length + 14) := by
  induction bits generalizing remainder with
  | nil => simp [divisionLoopAllocated]
  | cons incoming rest ih =>
      have hStep := stepWithAllocation_bound incoming remainder divisor hWidth
      have hNext := ih (BinaryDivisionWord.step incoming remainder divisor).2
        ((BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
      rw [divisionLoopAllocated]
      simp only [List.length_cons]
      nlinarith

def divisionLoopHeld (divisor : List Bool) : List Bool → List Bool → List Bool → ℕ
  | [], quotient, remainder => divisor.length + quotient.length + remainder.length + 2
  | incoming :: rest, quotient, remainder =>
      divisor.length + (incoming :: rest).length + quotient.length + remainder.length + 3 +
        stepStorage incoming remainder divisor +
          divisionLoopHeld divisor rest ((BinaryDivisionWord.step incoming remainder divisor).1 :: quotient)
            (BinaryDivisionWord.step incoming remainder divisor).2

theorem divisionLoopHeld_bound (divisor bits quotient remainder : List Bool)
    (hWidth : remainder.length = divisor.length) :
    divisionLoopHeld divisor bits quotient remainder ≤ (bits.length + 1) *
      (50 * (divisor.length + 2) ^ 2 + 2 * divisor.length + bits.length + quotient.length + 3) := by
  induction bits generalizing quotient remainder with
  | nil => simp only [divisionLoopHeld, List.length_nil, Nat.zero_add, Nat.one_mul, hWidth]; nlinarith
  | cons incoming rest ih =>
      have hStep := stepStorage_bound incoming remainder divisor hWidth
      have hNext := ih ((BinaryDivisionWord.step incoming remainder divisor).1 :: quotient)
        (BinaryDivisionWord.step incoming remainder divisor).2
        ((BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
      simp only [divisionLoopHeld, List.length_cons, hWidth] at hNext ⊢
      nlinarith

def divideWithAllocation (dividend divisor : List Bool) : (List Bool × List Bool) × ℕ :=
  let result := divisionLoopWithAllocation divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor)
  (result.1, 2 * dividend.length + divisor.length + result.2 + 2)

theorem divideWithAllocation_state (dividend divisor : List Bool) :
    (divideWithAllocation dividend divisor).1 = BinaryLongDivision.divide dividend divisor := by
  unfold divideWithAllocation
  dsimp only
  rw [divisionLoopWithAllocation_refines]
  rfl

theorem divideWithAllocation_bound (dividend divisor : List Bool) :
    (divideWithAllocation dividend divisor).2 ≤
      2 * dividend.length + divisor.length + 3 + dividend.length * (7 * divisor.length + 14) := by
  have h := divisionLoopAllocated_bound divisor dividend.reverse (BinaryLongDivision.zeroRemainder divisor)
    (BinaryLongDivision.zeroRemainder_length divisor)
  rw [List.length_reverse] at h
  unfold divideWithAllocation
  dsimp only
  rw [divisionLoopWithAllocation_refines]
  dsimp only
  omega

def divideStorage (dividend divisor : List Bool) : ℕ :=
  dividend.length + divisor.length + 2 * dividend.length + divisor.length +
    divisionLoopHeld divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor) +
      (divideWithAllocation dividend divisor).2

theorem divideStorage_bound (dividend divisor : List Bool) (W : ℕ)
    (hA : dividend.length ≤ W) (hB : divisor.length ≤ W) :
    divideStorage dividend divisor ≤ 500 * (W + 2) ^ 3 := by
  have hHeld := divisionLoopHeld_bound divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor)
    (BinaryLongDivision.zeroRemainder_length divisor)
  have hAllocated := divideWithAllocation_bound dividend divisor
  simp only [List.length_reverse, List.length_nil, Nat.add_zero] at hHeld
  have hHeldBound : divisionLoopHeld divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor) ≤
      (W + 1) * (50 * (W + 2) ^ 2 + 3 * W + 3) := by
    have hPower := Nat.pow_le_pow_left (Nat.add_le_add_right hB 2) 2
    have hInner : 50 * (divisor.length + 2) ^ 2 + 2 * divisor.length + dividend.length + 3 ≤
        50 * (W + 2) ^ 2 + 3 * W + 3 := by omega
    exact hHeld.trans (Nat.mul_le_mul (Nat.add_le_add_right hA 1) hInner)
  unfold divideStorage
  nlinarith

theorem divideWithAllocation_contract (dividend divisor : List Bool)
    (hD : 0 < BinaryBigEndian.littleValue divisor) (W : ℕ) (hA : dividend.length ≤ W) (hB : divisor.length ≤ W) :
    BinaryBigEndian.littleValue (divideWithAllocation dividend divisor).1.1 =
        BinaryBigEndian.littleValue dividend / BinaryBigEndian.littleValue divisor ∧
      BinaryBigEndian.littleValue (divideWithAllocation dividend divisor).1.2 =
        BinaryBigEndian.littleValue dividend % BinaryBigEndian.littleValue divisor ∧
      divideStorage dividend divisor ≤ 500 * (W + 2) ^ 3 := by
  rw [divideWithAllocation_state]
  exact ⟨(BinaryLongDivision.divide_div_mod dividend divisor hD).1,
    (BinaryLongDivision.divide_div_mod dividend divisor hD).2, divideStorage_bound dividend divisor W hA hB⟩

end Blotto.BinaryDivisionAllocation
