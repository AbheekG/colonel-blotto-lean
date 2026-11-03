import Blotto.BinaryMultiplication
import Blotto.FixedRegionAddressWork

/-! Fixed-region addresses form as base + index*stride + offset using
Boolean addition/multiplication. Operand words supply exact decoded values;
the conservative arithmetic envelope is quadratic in their common bit width.
Operand extraction/control/allocation costs are separate. -/

namespace Blotto.BinaryAddressFormation

def form (base index stride offset : List Bool) : List Bool :=
  let product := BinaryMultiplication.multiply index stride
  let displacement := BinaryAddition.add product offset
  BinaryAddition.add base displacement

theorem form_value (base index stride offset : List Bool) :
    BinaryBigEndian.littleValue (form base index stride offset) = BinaryBigEndian.littleValue base +
      BinaryBigEndian.littleValue index * BinaryBigEndian.littleValue stride + BinaryBigEndian.littleValue offset := by
  simp only [form, BinaryAddition.add_value, BinaryMultiplication.multiply_value]
  omega

theorem form_length (base index stride offset : List Bool) (S : ℕ)
    (hBase : base.length ≤ S) (hIndex : index.length ≤ S) (hStride : stride.length ≤ S) (hOffset : offset.length ≤ S) :
    (form base index stride offset).length ≤ 3 * S + 2 := by
  have hm := BinaryMultiplication.multiply_length index stride
  have ha := BinaryAddition.add_length (BinaryMultiplication.multiply index stride) offset
  have hb := BinaryAddition.add_length base (BinaryAddition.add (BinaryMultiplication.multiply index stride) offset)
  unfold form
  dsimp only
  omega

def work (base index stride offset : List Bool) : ℕ :=
  let product := BinaryMultiplication.multiply index stride
  let displacement := BinaryAddition.add product offset
  BinaryMultiplication.work index stride + BinaryAddition.bitWork product offset + BinaryAddition.bitWork base displacement

def workBound (S : ℕ) : ℕ := 66 * S * S + 179 * S + 67

theorem work_bound (base index stride offset : List Bool) (S : ℕ)
    (hBase : base.length ≤ S) (hIndex : index.length ≤ S) (hStride : stride.length ≤ S) (hOffset : offset.length ≤ S) :
    work base index stride offset ≤ workBound S := by
  have hm := BinaryMultiplication.work_bound index stride
  have hml := BinaryMultiplication.multiply_length index stride
  have ha := BinaryAddition.bitWork_bound (BinaryMultiplication.multiply index stride) offset
  have hal := BinaryAddition.add_length (BinaryMultiplication.multiply index stride) offset
  have hb := BinaryAddition.bitWork_bound base (BinaryAddition.add (BinaryMultiplication.multiply index stride) offset)
  have hMul : BinaryMultiplication.work index stride ≤ 1 + S * (22 * (3 * S + 2) + 3) := by
    have hs := Nat.mul_le_mul hIndex (show 22 * (2 * index.length + stride.length + 2) + 3 ≤ 22 * (3 * S + 2) + 3 by omega)
    exact hm.trans (Nat.add_le_add_left hs 1)
  have hAdd : BinaryAddition.bitWork (BinaryMultiplication.multiply index stride) offset ≤ 22 * (3 * S + 1) :=
    ha.trans (Nat.mul_le_mul_left 22 (by omega))
  have hLast : BinaryAddition.bitWork base (BinaryAddition.add (BinaryMultiplication.multiply index stride) offset) ≤ 22 * (3 * S + 2) :=
    hb.trans (Nat.mul_le_mul_left 22 (by omega))
  unfold work workBound
  dsimp only
  nlinarith

theorem payload_value (S value : ℕ) (h : value < 2 ^ S) :
    BinaryBigEndian.littleValue (BinaryPayload.bits S value) = value := by
  rw [BinaryBigEndian.littleValue_decode, BinaryPayload.decode_bits S value h]

def encodedAddress {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) : List Bool :=
  let S := FixedWordRegion.addressWidth base n W
  form (BinaryPayload.bits S base) (BinaryPayload.bits S j.val) (BinaryPayload.bits S W) (BinaryPayload.bits S offset.val)

theorem address_operand_bounds {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    base ≤ base + n * W + 1 ∧ j.val ≤ base + n * W + 1 ∧ W ≤ base + n * W + 1 ∧ offset.val ≤ base + n * W + 1 := by
  have hn : 1 ≤ n := by have hj := j.isLt; omega
  have hW : 1 ≤ W := by have hb := offset.isLt; omega
  have hj := j.isLt
  have hb := offset.isLt
  have hnW := Nat.mul_le_mul_left n hW
  have hWn := Nat.mul_le_mul_right W hn
  simp only [Nat.mul_one, Nat.one_mul] at hnW hWn
  omega

theorem encodedAddress_value {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    BinaryBigEndian.littleValue (encodedAddress base j offset) = FixedWordRegion.address base j offset := by
  have h := address_operand_bounds base j offset
  have hLimit := lt_pow_binaryWordWidth (base + n * W + 1)
  unfold encodedAddress
  dsimp only
  unfold FixedWordRegion.addressWidth
  rw [form_value, payload_value _ _ (h.1.trans_lt hLimit), payload_value _ _ (h.2.1.trans_lt hLimit),
    payload_value _ _ (h.2.2.1.trans_lt hLimit), payload_value _ _ (h.2.2.2.trans_lt hLimit)]
  rw [FixedWordRegion.address, FixedWordRegion.localAddress_val]
  omega

theorem encodedAddress_length {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    (encodedAddress base j offset).length ≤ 3 * FixedWordRegion.addressWidth base n W + 2 := by
  apply form_length <;> exact le_of_eq (BinaryPayload.bits_length _ _)

end Blotto.BinaryAddressFormation
