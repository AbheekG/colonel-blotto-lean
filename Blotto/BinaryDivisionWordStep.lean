import Blotto.BinaryCoinWordWork

/-! A restoring binary-division digit uses only Boolean shifts, borrow
subtraction and high-bit removal. The incoming dividend bit is retained in the
low position; numerical values and quotient equations occur only in proofs.
Equal-width leading-zero divisor/remainder words are accepted. -/

namespace Blotto.BinaryDivisionWord

def step (incoming : Bool) (remainder divisor : List Bool) : Bool × List Bool :=
  let shifted := incoming :: remainder
  let difference := BinaryBorrowWord.subtract shifted (divisor ++ [false]) false
  if difference.2 then (false, BinaryWordHighBit.drop shifted)
  else (true, BinaryWordHighBit.drop difference.1)

theorem input_lengths (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length) :
    (incoming :: remainder).length = (divisor ++ [false]).length := by simp [h]

theorem step_length (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length) : (step incoming remainder divisor).2.length = remainder.length := by
  have hs := BinaryBorrowWord.subtract_length (incoming :: remainder) (divisor ++ [false]) false
    (input_lengths incoming remainder divisor h)
  unfold step
  dsimp only
  split_ifs
  · rw [BinaryWordHighBit.drop_length]
    simp
  · rw [BinaryWordHighBit.drop_length, hs]
    simp

theorem step_digit (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length) :
    (step incoming remainder divisor).1 =
      decide (BinaryBigEndian.littleValue divisor ≤
        2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming) := by
  have hn := BinaryBorrowWord.subtract_noBorrow_iff (incoming :: remainder) (divisor ++ [false]) false
    (input_lengths incoming remainder divisor h)
  simp only [BinaryBigEndian.littleValue, BinaryWordHighBit.pad_value, BinaryBorrowWord.digit,
    Bool.false_eq_true, ite_false, Nat.add_zero] at hn
  cases hb : (BinaryBorrowWord.subtract (incoming :: remainder) (divisor ++ [false]) false).2
  · have hg := hn.mp hb
    change BinaryBigEndian.littleValue divisor ≤
      2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming at hg
    simp only [step, hb, Bool.false_eq_true, ite_false]
    exact (decide_eq_true hg).symm
  · have hg : ¬BinaryBigEndian.littleValue divisor ≤
        2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming := by
      intro he
      have hf := hn.mpr he
      rw [hb] at hf
      cases hf
    simp only [step, hb, ite_true]
    exact (decide_eq_false hg).symm

theorem step_balance (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length)
    (hlt : BinaryBigEndian.littleValue remainder < BinaryBigEndian.littleValue divisor) :
    2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming =
      BinaryBigEndian.littleValue divisor * BinaryBorrowWord.digit (step incoming remainder divisor).1 +
        BinaryBigEndian.littleValue (step incoming remainder divisor).2 := by
  have hn := BinaryBorrowWord.subtract_noBorrow_iff (incoming :: remainder) (divisor ++ [false]) false
    (input_lengths incoming remainder divisor h)
  have hDigit : BinaryBorrowWord.digit incoming ≤ 1 := by cases incoming <;> decide
  have hWidth := BinaryBorrowWord.littleValue_bounds divisor
  simp only [BinaryBigEndian.littleValue, BinaryWordHighBit.pad_value, BinaryBorrowWord.digit,
    Bool.false_eq_true, ite_false, Nat.add_zero] at hn
  cases hb : (BinaryBorrowWord.subtract (incoming :: remainder) (divisor ++ [false]) false).2
  · have hg := hn.mp hb
    have hv := BinaryBorrowWord.subtract_value (incoming :: remainder) (divisor ++ [false]) false
      (input_lengths incoming remainder divisor h) hb
    have hs := BinaryBorrowWord.subtract_length (incoming :: remainder) (divisor ++ [false]) false
      (input_lengths incoming remainder divisor h)
    simp only [BinaryBigEndian.littleValue, BinaryWordHighBit.pad_value, BinaryBorrowWord.digit,
      Bool.false_eq_true, ite_false, Nat.add_zero] at hv
    have hDrop : BinaryBigEndian.littleValue
        (BinaryBorrowWord.subtract (incoming :: remainder) (divisor ++ [false]) false).1 <
        2 ^ ((BinaryBorrowWord.subtract (incoming :: remainder) (divisor ++ [false]) false).1.length - 1) := by
      rw [hs]
      simp only [List.length_cons, Nat.add_sub_cancel, hv]
      rw [h]
      change _ + BinaryBorrowWord.digit incoming - _ < _
      omega
    simp only [step, hb, Bool.false_eq_true, ite_false]
    rw [BinaryWordHighBit.drop_value _ hDrop, hv]
    change 2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming =
      BinaryBigEndian.littleValue divisor * 1 +
        (2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming - BinaryBigEndian.littleValue divisor)
    unfold BinaryBorrowWord.digit at *
    omega
  · have hg : ¬BinaryBigEndian.littleValue divisor ≤
        2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming := by
      intro he
      have hf := hn.mpr he
      rw [hb] at hf
      cases hf
    have hDrop : BinaryBigEndian.littleValue (incoming :: remainder) <
        2 ^ ((incoming :: remainder).length - 1) := by
      simp only [BinaryBigEndian.littleValue, List.length_cons, Nat.add_sub_cancel]
      rw [h]
      change _ + BinaryBorrowWord.digit incoming < _
      omega
    simp only [step, hb, ite_true]
    rw [BinaryWordHighBit.drop_value _ hDrop]
    change _ = _ * 0 + (2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming)
    simp

theorem step_remainder_lt (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length)
    (hlt : BinaryBigEndian.littleValue remainder < BinaryBigEndian.littleValue divisor) :
    BinaryBigEndian.littleValue (step incoming remainder divisor).2 < BinaryBigEndian.littleValue divisor := by
  have hb := step_balance incoming remainder divisor h hlt
  have hd := step_digit incoming remainder divisor h
  have hDigit : BinaryBorrowWord.digit incoming ≤ 1 := by cases incoming <;> decide
  cases hOut : (step incoming remainder divisor).1
  · rw [hOut] at hb hd
    have hn : ¬ BinaryBigEndian.littleValue divisor ≤
        2 * BinaryBigEndian.littleValue remainder + BinaryBorrowWord.digit incoming := by
      exact of_decide_eq_false hd.symm
    change _ = _ * 0 + _ at hb
    omega
  · rw [hOut] at hb
    change _ = _ * 1 + _ at hb
    omega

def chosenResidual (incoming : Bool) (remainder divisor : List Bool) : List Bool :=
  let shifted := incoming :: remainder
  let difference := BinaryBorrowWord.subtract shifted (divisor ++ [false]) false
  if difference.2 then shifted else difference.1

theorem chosenResidual_length (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length) :
    (chosenResidual incoming remainder divisor).length = remainder.length + 1 := by
  have hs := BinaryBorrowWord.subtract_length (incoming :: remainder) (divisor ++ [false]) false
    (input_lengths incoming remainder divisor h)
  unfold chosenResidual
  dsimp only
  split_ifs
  · rfl
  · simpa only [List.length_cons] using hs

-- The same conservative Boolean/read/cons/reversal accounting as the verified
-- coin digit, with one incoming-bit read added explicitly.
def bitWork (incoming : Bool) (remainder divisor : List Bool) : ℕ :=
  2 + (divisor.length + 1) + 8 * (remainder.length + 1) + 2 * (remainder.length + 1) +
    2 * (remainder.length + 1) + BinaryBorrowWord.visits (incoming :: remainder) (divisor ++ [false]) +
    BinaryWordHighBit.visits (chosenResidual incoming remainder divisor) + 2 * remainder.length + 1

theorem bitWork_bound (incoming : Bool) (remainder divisor : List Bool)
    (h : remainder.length = divisor.length) : bitWork incoming remainder divisor ≤ 17 * remainder.length + 20 := by
  have hs := BinaryBorrowWord.visits_eq (incoming :: remainder) (divisor ++ [false])
    (input_lengths incoming remainder divisor h)
  have hd := BinaryWordHighBit.visits_bound (chosenResidual incoming remainder divisor)
  rw [chosenResidual_length incoming remainder divisor h] at hd
  simp only [List.length_cons] at hs
  unfold bitWork
  omega

end Blotto.BinaryDivisionWord
