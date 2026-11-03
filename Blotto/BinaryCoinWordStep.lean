import Blotto.BinaryWordHighBit
import Blotto.FixedDenominatorCoin

/-! A fair-bit coin digit and residual use a fixed-width Boolean subtraction.
Doubling adds one low zero; removing the zero high bit prevents width growth.
The numerical equations match the retained fixed-denominator coin exactly. -/

namespace Blotto.BinaryCoinWord

def step (a b : List Bool) : Bool × List Bool :=
  let doubled := false :: a
  let result := BinaryBorrowWord.subtract doubled (b ++ [false]) false
  if result.2 then (false, BinaryWordHighBit.drop doubled)
  else (true, BinaryWordHighBit.drop result.1)

theorem input_lengths (a b : List Bool) (h : a.length = b.length) :
    (false :: a).length = (b ++ [false]).length := by simp [h]

theorem step_length (a b : List Bool) (h : a.length = b.length) : (step a b).2.length = a.length := by
  have hs := BinaryBorrowWord.subtract_length (false :: a) (b ++ [false]) false (input_lengths a b h)
  unfold step
  dsimp only
  split_ifs
  · rw [BinaryWordHighBit.drop_length]
    simp
  · rw [BinaryWordHighBit.drop_length, hs]
    simp

theorem step_digit (a b : List Bool) (h : a.length = b.length) :
    (step a b).1 = denominatorDigit (BinaryBigEndian.littleValue a) (BinaryBigEndian.littleValue b) := by
  have hn := BinaryBorrowWord.subtract_noBorrow_iff (false :: a) (b ++ [false]) false (input_lengths a b h)
  simp only [BinaryBigEndian.littleValue, Bool.false_eq_true, ite_false, Nat.add_zero,
    BinaryWordHighBit.pad_value, BinaryBorrowWord.digit] at hn
  cases hb : (BinaryBorrowWord.subtract (false :: a) (b ++ [false]) false).2
  · have hg : BinaryBigEndian.littleValue b ≤ 2 * BinaryBigEndian.littleValue a := hn.mp hb
    simp [step, hb, denominatorDigit, hg]
  · have hg : ¬ BinaryBigEndian.littleValue b ≤ 2 * BinaryBigEndian.littleValue a := by
      intro he
      have hf := hn.mpr he
      rw [hb] at hf
      cases hf
    simp [step, hb, denominatorDigit, hg]

theorem step_residual (a b : List Bool) (h : a.length = b.length)
    (hlt : BinaryBigEndian.littleValue a < BinaryBigEndian.littleValue b) :
    BinaryBigEndian.littleValue (step a b).2 =
      numeratorResidual (BinaryBigEndian.littleValue a) (BinaryBigEndian.littleValue b) := by
  have hn := BinaryBorrowWord.subtract_noBorrow_iff (false :: a) (b ++ [false]) false (input_lengths a b h)
  have hWidth := BinaryBorrowWord.littleValue_bounds b
  simp only [BinaryBigEndian.littleValue, Bool.false_eq_true, ite_false, Nat.add_zero,
    BinaryWordHighBit.pad_value, BinaryBorrowWord.digit] at hn
  cases hb : (BinaryBorrowWord.subtract (false :: a) (b ++ [false]) false).2
  · have hg : BinaryBigEndian.littleValue b ≤ 2 * BinaryBigEndian.littleValue a := hn.mp hb
    have hv := BinaryBorrowWord.subtract_value (false :: a) (b ++ [false]) false (input_lengths a b h) hb
    have hs := BinaryBorrowWord.subtract_length (false :: a) (b ++ [false]) false (input_lengths a b h)
    simp only [BinaryBigEndian.littleValue, Bool.false_eq_true, ite_false,
      BinaryWordHighBit.pad_value, BinaryBorrowWord.digit, Nat.add_zero] at hv
    have hDrop : BinaryBigEndian.littleValue (BinaryBorrowWord.subtract (false :: a) (b ++ [false]) false).1 <
        2 ^ ((BinaryBorrowWord.subtract (false :: a) (b ++ [false]) false).1.length - 1) := by
      rw [hs]
      simp only [List.length_cons, Nat.add_sub_cancel, hv]
      rw [h] at ⊢
      omega
    simp only [step, hb, Bool.false_eq_true, ite_false]
    rw [BinaryWordHighBit.drop_value _ hDrop, hv]
    simp [numeratorResidual, denominatorDigit, hg]
  · have hg : ¬ BinaryBigEndian.littleValue b ≤ 2 * BinaryBigEndian.littleValue a := by
      intro he
      have hf := hn.mpr he
      rw [hb] at hf
      cases hf
    have hDrop : BinaryBigEndian.littleValue (false :: a) < 2 ^ ((false :: a).length - 1) := by
      simp only [BinaryBigEndian.littleValue, Bool.false_eq_true, ite_false,
        Nat.add_zero, List.length_cons, Nat.add_sub_cancel]
      rw [h]
      omega
    simp only [step, hb, ite_true]
    rw [BinaryWordHighBit.drop_value _ hDrop]
    simp [numeratorResidual, denominatorDigit, hg, BinaryBigEndian.littleValue]

theorem step_normalized (a b : List Bool) (h : a.length = b.length)
    (hlt : BinaryBigEndian.littleValue a < BinaryBigEndian.littleValue b) :
    BinaryBigEndian.littleValue (step a b).2 < BinaryBigEndian.littleValue b := by
  rw [step_residual a b h hlt]
  unfold numeratorResidual denominatorDigit
  split_ifs <;> simp_all only [decide_eq_true_eq] <;> omega

end Blotto.BinaryCoinWord
