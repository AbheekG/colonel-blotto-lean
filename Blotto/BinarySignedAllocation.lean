import Blotto.BinaryNormalizationAllocation
import Blotto.BinarySignedMagnitude

/-! Structural signed-magnitude allocation. Padding copies the original
prefix and allocates its false suffix; opposite signs execute the actual
forward borrow and, only if needed, the backward borrow. Storage retains the
inputs, padded buffers, both candidate results and all primitive frames until
return. This abstract Boolean/list-cell model makes no physical heap claim. -/

namespace Blotto.BinarySignedAllocation
open BinarySignedMagnitude

def padWithAllocation (W : ℕ) (bits : List Bool) : List Bool × ℕ :=
  (pad W bits, bits.length + (W - bits.length) + 2)

theorem padWithAllocation_state (W : ℕ) (bits : List Bool) :
    (padWithAllocation W bits).1 = pad W bits := rfl

theorem padWithAllocation_bound (W : ℕ) (bits : List Bool) (h : bits.length ≤ W) :
    (padWithAllocation W bits).2 ≤ W + 2 := by unfold padWithAllocation; omega

def differenceWithAllocation (first second : List Bool) : Word × ℕ :=
  let W := max first.length second.length
  let a := padWithAllocation W first
  let b := padWithAllocation W second
  let forward := BinaryDivisionAllocation.borrowWithAllocation a.1 b.1 false []
  if forward.1.2 then
    let backward := BinaryDivisionAllocation.borrowWithAllocation b.1 a.1 false []
    (⟨true, backward.1.1⟩, a.2 + b.2 + forward.2 + backward.2 + 4)
  else (⟨false, forward.1.1⟩, a.2 + b.2 + forward.2 + 4)

theorem differenceWithAllocation_state (first second : List Bool) :
    (differenceWithAllocation first second).1 = difference first second := by
  unfold differenceWithAllocation difference BinaryBorrowWord.subtract
  dsimp only [padWithAllocation]
  rw [BinaryDivisionAllocation.borrowWithAllocation_refines]
  dsimp only
  split
  · rw [BinaryDivisionAllocation.borrowWithAllocation_refines]
  · rfl

theorem differenceWithAllocation_bound (first second : List Bool) (W : ℕ)
    (hA : first.length ≤ W) (hB : second.length ≤ W) :
    (differenceWithAllocation first second).2 ≤ 10 * (W + 1) := by
  let M := max first.length second.length
  have hM : M ≤ W := max_le hA hB
  have ha : (pad M first).length = M := pad_length M first (Nat.le_max_left _ _)
  have hb : (pad M second).length = M := pad_length M second (Nat.le_max_right _ _)
  have hpA := padWithAllocation_bound M first (Nat.le_max_left _ _)
  have hpB := padWithAllocation_bound M second (Nat.le_max_right _ _)
  have hf := BinaryDivisionAllocation.borrowAllocated_bound (pad M first) (pad M second) false []
  have hr := BinaryDivisionAllocation.borrowAllocated_bound (pad M second) (pad M first) false []
  simp only [ha, hb, List.length_nil, Nat.add_zero] at hf hr
  dsimp only [M] at hf hr hpA hpB hM
  unfold differenceWithAllocation
  dsimp only [padWithAllocation]
  rw [BinaryDivisionAllocation.borrowWithAllocation_refines]
  dsimp only
  split
  · rw [BinaryDivisionAllocation.borrowWithAllocation_refines]
    dsimp only
    change _ ≤ 10 * (W + 1)
    change first.length + (M - first.length) + 2 ≤ M + 2 at hpA
    change second.length + (M - second.length) + 2 ≤ M + 2 at hpB
    omega
  · dsimp only
    change first.length + (M - first.length) + 2 ≤ M + 2 at hpA
    change second.length + (M - second.length) + 2 ≤ M + 2 at hpB
    omega

def differenceStorage (first second : List Bool) : ℕ :=
  let M := max first.length second.length
  let a := pad M first
  let b := pad M second
  first.length + second.length + a.length + b.length +
    (BinaryBorrowWord.subtract a b false).1.length +
    (BinaryBorrowWord.subtract b a false).1.length + 6 +
      BinaryDivisionAllocation.borrowStorage a b + BinaryDivisionAllocation.borrowStorage b a +
        (differenceWithAllocation first second).2

theorem differenceStorage_bound (first second : List Bool) (W : ℕ)
    (hA : first.length ≤ W) (hB : second.length ≤ W) :
    differenceStorage first second ≤ 40 * (W + 1) ^ 2 := by
  let M := max first.length second.length
  have hM : M ≤ W := max_le hA hB
  have ha : (pad M first).length = M := pad_length M first (Nat.le_max_left _ _)
  have hb : (pad M second).length = M := pad_length M second (Nat.le_max_right _ _)
  have hf := BinaryDivisionAllocation.borrowStorage_bound (pad M first) (pad M second) W (ha.le.trans hM) (hb.le.trans hM)
  have hr := BinaryDivisionAllocation.borrowStorage_bound (pad M second) (pad M first) W (hb.le.trans hM) (ha.le.trans hM)
  have hfl := BinaryBorrowWord.subtract_length (pad M first) (pad M second) false (ha.trans hb.symm)
  have hrl := BinaryBorrowWord.subtract_length (pad M second) (pad M first) false (hb.trans ha.symm)
  have hc := differenceWithAllocation_bound first second W hA hB
  unfold differenceStorage
  dsimp only
  change first.length + second.length + (pad M first).length + (pad M second).length +
    (BinaryBorrowWord.subtract (pad M first) (pad M second) false).1.length +
    (BinaryBorrowWord.subtract (pad M second) (pad M first) false).1.length + 6 +
    BinaryDivisionAllocation.borrowStorage (pad M first) (pad M second) +
    BinaryDivisionAllocation.borrowStorage (pad M second) (pad M first) +
    (differenceWithAllocation first second).2 ≤ 40 * (W + 1) ^ 2
  rw [hfl, hrl, ha, hb]
  nlinarith

def addWithAllocation (first second : Word) : Word × ℕ :=
  if first.negative = second.negative then
    let added := BinaryArithmeticAllocation.addWithAllocation first.bits second.bits
    (⟨first.negative, added.1⟩, added.2 + 3)
  else if first.negative then
    let result := differenceWithAllocation second.bits first.bits
    (result.1, result.2 + 3)
  else
    let result := differenceWithAllocation first.bits second.bits
    (result.1, result.2 + 3)

theorem addWithAllocation_state (first second : Word) :
    (addWithAllocation first second).1 = BinarySignedMagnitude.add first second := by
  unfold addWithAllocation BinarySignedMagnitude.add
  split
  · rw [BinaryArithmeticAllocation.addWithAllocation_refines]
  · split <;> rw [differenceWithAllocation_state]

theorem addWithAllocation_bound (first second : Word) (W : ℕ)
    (hA : first.bits.length ≤ W) (hB : second.bits.length ≤ W) :
    (addWithAllocation first second).2 ≤ 15 * (W + 1) := by
  have ha := (BinaryArithmeticAllocation.addWithAllocation_contract first.bits second.bits W hA hB).2.1
  have hd := differenceWithAllocation_bound first.bits second.bits W hA hB
  have hr := differenceWithAllocation_bound second.bits first.bits W hB hA
  unfold addWithAllocation
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

def addStorage (first second : Word) : ℕ :=
  first.bits.length + second.bits.length + 4 +
    if first.negative = second.negative then BinaryArithmeticAllocation.addStorage first.bits second.bits
    else if first.negative then differenceStorage second.bits first.bits else differenceStorage first.bits second.bits

theorem addStorage_bound (first second : Word) (W : ℕ)
    (hA : first.bits.length ≤ W) (hB : second.bits.length ≤ W) :
    addStorage first second ≤ 50 * (W + 1) ^ 2 := by
  have ha := BinaryArithmeticAllocation.addStorage_bound first.bits second.bits W hA hB
  have hd := differenceStorage_bound first.bits second.bits W hA hB
  have hr := differenceStorage_bound second.bits first.bits W hB hA
  unfold addStorage
  split
  · nlinarith
  · split <;> nlinarith

def subtractWithAllocation (first second : Word) : Word × ℕ :=
  let result := addWithAllocation first (BinarySignedMagnitude.negate second)
  (result.1, result.2 + 1)

theorem subtractWithAllocation_state (first second : Word) :
    (subtractWithAllocation first second).1 = BinarySignedMagnitude.subtract first second :=
  addWithAllocation_state first (BinarySignedMagnitude.negate second)

def multiplyWithAllocation (first second : Word) : Word × ℕ :=
  let result := BinaryArithmeticAllocation.multiplyWithAllocation first.bits second.bits
  (⟨Bool.xor first.negative second.negative, result.1⟩, result.2 + 2)

theorem multiplyWithAllocation_state (first second : Word) :
    (multiplyWithAllocation first second).1 = BinarySignedMagnitude.multiply first second := by
  unfold multiplyWithAllocation BinarySignedMagnitude.multiply
  rw [BinaryArithmeticAllocation.multiplyWithAllocation_refines]

theorem multiplyWithAllocation_bound (first second : Word) (W : ℕ)
    (hA : first.bits.length ≤ W) (hB : second.bits.length ≤ W) :
    (multiplyWithAllocation first second).2 ≤ 25 * (W + 1) ^ 2 := by
  have h := (BinaryArithmeticAllocation.multiplyWithAllocation_contract first.bits second.bits W hA hB).2.1
  unfold multiplyWithAllocation
  dsimp only
  nlinarith

def multiplyStorage (first second : Word) : ℕ :=
  first.bits.length + second.bits.length + 3 + BinaryArithmeticAllocation.multiplyStorage first.bits second.bits

theorem multiplyStorage_bound (first second : Word) (W : ℕ)
    (hA : first.bits.length ≤ W) (hB : second.bits.length ≤ W) :
    multiplyStorage first second ≤ 210 * (W + 1) ^ 3 := by
  have h := BinaryArithmeticAllocation.multiplyStorage_bound first.bits second.bits W hA hB
  have hp : W + 1 ≤ (W + 1) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 1) (by omega : 1 ≤ 3))
  unfold multiplyStorage
  nlinarith

end Blotto.BinarySignedAllocation
