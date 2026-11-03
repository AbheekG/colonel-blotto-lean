import Blotto.BinaryMultiplication

/-! Structural Boolean/list-cell allocation for the actual full-adder and
schoolbook multiplier. Every cons/reversal output is charged as it occurs;
control frames and held inputs are explicit. The conservative retained-buffer
model releases no newly allocated cell until the call returns, so allocation
sums bound its live payload without an allocator/GC assumption. This is an
abstract list-cell contract, not physical native heap or instruction timing. -/

namespace Blotto.BinaryArithmeticAllocation

def addLoopAllocated : List Bool → List Bool → Bool → List Bool → ℕ
  | [], [], carry, acc => if carry then 1 + (acc.length + 1) else acc.length
  | a :: rest, [], carry, acc =>
      2 + addLoopAllocated rest [] (BinaryAddition.nextCarry a false carry)
        (BinaryAddition.sumBit a false carry :: acc)
  | [], b :: rest, carry, acc =>
      2 + addLoopAllocated [] rest (BinaryAddition.nextCarry false b carry)
        (BinaryAddition.sumBit false b carry :: acc)
  | a :: as, b :: bs, carry, acc =>
      2 + addLoopAllocated as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry :: acc)

def addLoopWithAllocation : List Bool → List Bool → Bool → List Bool → List Bool × ℕ
  | [], [], carry, acc =>
      if carry then ((true :: acc).reverse, 1 + (acc.length + 1)) else (acc.reverse, acc.length)
  | a :: rest, [], carry, acc =>
      let next := addLoopWithAllocation rest [] (BinaryAddition.nextCarry a false carry)
        (BinaryAddition.sumBit a false carry :: acc)
      (next.1, 2 + next.2)
  | [], b :: rest, carry, acc =>
      let next := addLoopWithAllocation [] rest (BinaryAddition.nextCarry false b carry)
        (BinaryAddition.sumBit false b carry :: acc)
      (next.1, 2 + next.2)
  | a :: as, b :: bs, carry, acc =>
      let next := addLoopWithAllocation as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry :: acc)
      (next.1, 2 + next.2)

theorem addLoopWithAllocation_refines (a b : List Bool) (carry : Bool) (acc : List Bool) :
    addLoopWithAllocation a b carry acc =
      (BinaryAddition.loop a b carry acc, addLoopAllocated a b carry acc) := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil => cases carry <;> simp [addLoopWithAllocation, BinaryAddition.loop, addLoopAllocated]
      | cons bit rest ih => rw [addLoopWithAllocation, ih]; simp only [BinaryAddition.loop, addLoopAllocated]
  | cons bit rest ih =>
      cases b with
      | nil => rw [addLoopWithAllocation, ih]; simp only [BinaryAddition.loop, addLoopAllocated]
      | cons other tail => rw [addLoopWithAllocation, ih]; simp only [BinaryAddition.loop, addLoopAllocated]

theorem addLoopAllocated_bound (a b : List Bool) (carry : Bool) (acc : List Bool) :
    addLoopAllocated a b carry acc ≤ 3 * max a.length b.length + acc.length + 2 := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil => cases carry <;> simp only [addLoopAllocated, List.length_nil, Nat.max_self, Nat.mul_zero, Nat.zero_add,
          Bool.false_eq_true, ite_false, ite_true] <;> omega
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry :: acc)
          simp only [addLoopAllocated, List.length_cons, List.length_nil] at h ⊢
          omega
  | cons bit rest ih =>
      cases b with
      | nil =>
          have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry :: acc)
          simp only [addLoopAllocated, List.length_cons, List.length_nil] at h ⊢
          omega
      | cons other tail =>
          have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry :: acc)
          simp only [addLoopAllocated, List.length_cons] at h ⊢
          omega

-- Each recursive entry retains its two unconsumed inputs, reversed prefix,
-- carry and one control record. Parent-frame payloads are conservatively kept.
def addLoopHeldPayload : List Bool → List Bool → Bool → List Bool → ℕ
  | [], [], _carry, acc => acc.length + 2
  | a :: rest, [], carry, acc =>
      (a :: rest).length + acc.length + 2 + addLoopHeldPayload rest []
        (BinaryAddition.nextCarry a false carry) (BinaryAddition.sumBit a false carry :: acc)
  | [], b :: rest, carry, acc =>
      (b :: rest).length + acc.length + 2 + addLoopHeldPayload [] rest
        (BinaryAddition.nextCarry false b carry) (BinaryAddition.sumBit false b carry :: acc)
  | a :: as, b :: bs, carry, acc =>
      (a :: as).length + (b :: bs).length + acc.length + 2 + addLoopHeldPayload as bs
        (BinaryAddition.nextCarry a b carry) (BinaryAddition.sumBit a b carry :: acc)

theorem addLoopHeldPayload_bound (a b : List Bool) (carry : Bool) (acc : List Bool) :
    addLoopHeldPayload a b carry acc ≤
      (max a.length b.length + 1) * (a.length + b.length + acc.length + 2) := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil => simp [addLoopHeldPayload]
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry :: acc)
          simp only [addLoopHeldPayload, List.length_cons, List.length_nil, Nat.zero_max, Nat.zero_add] at h ⊢
          nlinarith
  | cons bit rest ih =>
      cases b with
      | nil =>
          have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry :: acc)
          simp only [addLoopHeldPayload, List.length_cons, List.length_nil, Nat.max_zero, Nat.add_zero] at h ⊢
          nlinarith
      | cons other tail =>
          have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry :: acc)
          simp only [addLoopHeldPayload, List.length_cons] at h ⊢
          have hm : max rest.length tail.length + 1 = max (rest.length + 1) (tail.length + 1) := by omega
          rw [← hm]
          nlinarith

def addWithAllocation (a b : List Bool) : List Bool × ℕ := addLoopWithAllocation a b false []

theorem addWithAllocation_refines (a b : List Bool) :
    addWithAllocation a b = (BinaryAddition.add a b, addLoopAllocated a b false []) :=
  addLoopWithAllocation_refines a b false []

def addStorage (a b : List Bool) : ℕ :=
  addLoopHeldPayload a b false [] + addLoopAllocated a b false []

theorem addStorage_bound (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    addStorage a b ≤ 8 * (W + 1) ^ 2 := by
  have hHeld := addLoopHeldPayload_bound a b false []
  have hAllocated := addLoopAllocated_bound a b false []
  simp only [List.length_nil, Nat.add_zero] at hHeld hAllocated
  have hMax : max a.length b.length ≤ W := max_le ha hb
  unfold addStorage
  nlinarith

def multiplyAllocated : List Bool → List Bool → ℕ
  | [], _other => 1
  | bit :: rest, other =>
      multiplyAllocated rest other + 3 +
        if bit then addLoopAllocated other (false :: BinaryMultiplication.multiply rest other) false [] else 0

def multiplyWithAllocation : List Bool → List Bool → List Bool × ℕ
  | [], _other => ([], 1)
  | bit :: rest, other =>
      let earlier := multiplyWithAllocation rest other
      let shifted := false :: earlier.1
      if bit then
        let added := addWithAllocation other shifted
        (added.1, earlier.2 + 3 + added.2)
      else (shifted, earlier.2 + 3)

theorem multiplyWithAllocation_refines (a b : List Bool) :
    multiplyWithAllocation a b = (BinaryMultiplication.multiply a b, multiplyAllocated a b) := by
  induction a with
  | nil => rfl
  | cons bit rest ih =>
      rw [multiplyWithAllocation, ih]
      cases bit
      · rfl
      · rw [addWithAllocation_refines]
        rfl

theorem multiplyAllocated_bound (a b : List Bool) :
    multiplyAllocated a b ≤ 1 + a.length * (6 * a.length + 3 * b.length + 8) := by
  induction a with
  | nil => simp [multiplyAllocated]
  | cons bit rest ih =>
      have hLength := BinaryMultiplication.multiply_length rest b
      have hAdd := addLoopAllocated_bound b (false :: BinaryMultiplication.multiply rest b) false []
      simp only [List.length_nil, Nat.add_zero, List.length_cons] at hAdd
      have hMax : max b.length (BinaryMultiplication.multiply rest b).length.succ ≤ 2 * rest.length + b.length + 1 := by omega
      have hABound : addLoopAllocated b (false :: BinaryMultiplication.multiply rest b) false [] ≤
          6 * rest.length + 3 * b.length + 5 := by omega
      cases bit <;> simp only [multiplyAllocated, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> nlinarith

-- A multiplication frame retains unconsumed first input, complete second
-- input and its child/shifted product; the selected add may retain all of its
-- own frames. This intentionally overcounts any sharing of unchanged inputs.
def multiplyHeldPayload : List Bool → List Bool → ℕ
  | [], other => other.length + 2
  | bit :: rest, other =>
      (bit :: rest).length + other.length + (false :: BinaryMultiplication.multiply rest other).length + 3 +
        multiplyHeldPayload rest other +
          if bit then addLoopHeldPayload other (false :: BinaryMultiplication.multiply rest other) false [] else 0

theorem multiplyHeldPayload_bound (a b : List Bool) :
    multiplyHeldPayload a b ≤ 20 * (a.length + b.length + 1) ^ 3 := by
  induction a with
  | nil =>
      simp only [multiplyHeldPayload, List.length_nil, Nat.zero_add]
      have hLinear : b.length + 1 ≤ (b.length + 1) ^ 3 := by
        have hSquare : 1 ≤ (b.length + 1) ^ 2 := one_le_pow₀ (by omega)
        nlinarith
      nlinarith
  | cons bit rest ih =>
      have hLength := BinaryMultiplication.multiply_length rest b
      have hAdd := addLoopHeldPayload_bound b (false :: BinaryMultiplication.multiply rest b) false []
      simp only [List.length_nil, Nat.add_zero, List.length_cons] at hAdd
      have hMax : max b.length ((BinaryMultiplication.multiply rest b).length + 1) ≤ 2 * rest.length + b.length + 1 := by omega
      have hProduct : addLoopHeldPayload b (false :: BinaryMultiplication.multiply rest b) false [] ≤
          (2 * rest.length + b.length + 2) * (2 * rest.length + 2 * b.length + 3) := by
        have hm := Nat.mul_le_mul (Nat.add_le_add_right hMax 1)
          (show b.length + ((BinaryMultiplication.multiply rest b).length + 1) + 2 ≤ 2 * rest.length + 2 * b.length + 3 by omega)
        exact hAdd.trans hm
      cases bit <;> simp only [multiplyHeldPayload, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> nlinarith

def multiplyStorage (a b : List Bool) : ℕ := multiplyHeldPayload a b + multiplyAllocated a b

theorem multiplyStorage_bound (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    multiplyStorage a b ≤ 200 * (W + 1) ^ 3 := by
  have hHeld := multiplyHeldPayload_bound a b
  have hAllocated := multiplyAllocated_bound a b
  have hSize : a.length + b.length + 1 ≤ 2 * (W + 1) := by omega
  have hPow := Nat.pow_le_pow_left hSize 3
  have hHeldBound := hHeld.trans (Nat.mul_le_mul_left 20 hPow)
  have hLinear : W + 1 ≤ (W + 1) ^ 3 := by
    have hSquare : 1 ≤ (W + 1) ^ 2 := one_le_pow₀ (by omega)
    nlinarith
  have hSquare : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold multiplyStorage
  nlinarith

theorem addWithAllocation_contract (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    BinaryBigEndian.littleValue (addWithAllocation a b).1 = BinaryBigEndian.littleValue a + BinaryBigEndian.littleValue b ∧
      (addWithAllocation a b).2 ≤ 3 * W + 2 ∧ addStorage a b ≤ 8 * (W + 1) ^ 2 := by
  rw [addWithAllocation_refines]
  have h := addLoopAllocated_bound a b false []
  simp only [List.length_nil, Nat.add_zero] at h
  refine ⟨BinaryAddition.add_value a b, ?_, addStorage_bound a b W ha hb⟩
  have hMax : max a.length b.length ≤ W := max_le ha hb
  omega

theorem multiplyWithAllocation_contract (a b : List Bool) (W : ℕ) (ha : a.length ≤ W) (hb : b.length ≤ W) :
    BinaryBigEndian.littleValue (multiplyWithAllocation a b).1 = BinaryBigEndian.littleValue a * BinaryBigEndian.littleValue b ∧
      (multiplyWithAllocation a b).2 ≤ 1 + W * (9 * W + 8) ∧ multiplyStorage a b ≤ 200 * (W + 1) ^ 3 := by
  rw [multiplyWithAllocation_refines]
  have h := multiplyAllocated_bound a b
  refine ⟨BinaryMultiplication.multiply_value a b, ?_, multiplyStorage_bound a b W ha hb⟩
  nlinarith

end Blotto.BinaryArithmeticAllocation
