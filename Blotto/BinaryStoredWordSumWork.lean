import Blotto.BinaryPRGPreparationWork
import Blotto.BinaryFactoryHeight
import Blotto.RationalHeightAdd

/-! Arbitrary canonical decoded words, including rejected games, derive a
linear sum-height credit from their stored lengths. Native addition work is
polynomial in that credit; no accepted-game/unit-mass promise is assumed. -/

namespace Blotto.BinaryStoredWordSumWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition

theorem stored_value_height (word : SignedWord) (h : Valid word) : RationalHeight (value word) (width word) := by
  have hn : BinaryBigEndian.littleValue word.numerator < 2 ^ width word := by
    have he := BinaryBigEndian.value_bounds word.numerator.reverse
    rw [BinaryBigEndian.value_reverse,List.length_reverse] at he
    exact he.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_max_left _ _))
  have hd : BinaryBigEndian.littleValue word.denominator < 2 ^ width word := by
    have he := BinaryBigEndian.value_bounds word.denominator.reverse
    rw [BinaryBigEndian.value_reverse,List.length_reverse] at he
    exact he.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_max_right _ _))
  have hp := RationalHeight.fraction (BinaryBigEndian.littleValue word.numerator : ℤ) _ _ h
    (by simpa using hn) hd
  unfold value
  cases word.negative
  · simpa only [Bool.false_eq_true,ite_false,Int.cast_natCast] using hp
  · simpa only [ite_true,neg_div,Int.cast_natCast] using hp.neg

def credit (words : List SignedWord) : ℕ := 1 + (words.map (fun word => width word + 1)).sum

theorem credit_cons (word : SignedWord) (rest : List SignedWord) : credit (word :: rest) = width word + credit rest + 1 := by
  simp only [credit,List.map_cons,List.sum_cons]
  omega

theorem credit_tail (word : SignedWord) (rest : List SignedWord) : credit rest ≤ credit (word :: rest) := by rw [credit_cons]; omega

theorem credit_member (words : List SignedWord) (word : SignedWord) (h : word ∈ words) : width word ≤ credit words := by
  induction words with
  | nil => cases h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with he | ht
      · subst word; rw [credit_cons]; omega
      · exact (ih ht).trans (credit_tail head rest)

theorem sum_height (words : List SignedWord) (hC : ∀ word ∈ words, CanonicalWord word) :
    RationalHeight (value (sumWords words)) (credit words) := by
  induction words with
  | nil => simpa only [sumWords,zero_value,credit,List.map_nil,List.sum_nil,Nat.add_zero] using
      (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight])
  | cons word rest ih =>
      have ht : ∀ item ∈ rest, CanonicalWord item := fun item hi => hC item (by simp [hi])
      rw [sumWords,apply_value .add _ _ (hC word (by simp)).1 (sumWords_canonical rest ht).1]
      have hh := (stored_value_height word (hC word (by simp)).1).add (ih ht)
      simpa only [RealArithmeticOp.applyRat,credit_cons] using hh

def sumWithWork : List SignedWord → SignedWord × ℕ
  | [] => (zero,0)
  | word :: rest =>
      let tail := sumWithWork rest
      let head := applyWithWork .add word tail.1
      (head.1,tail.2 + head.2)

theorem sumWithWork_state (words : List SignedWord) : (sumWithWork words).1 = sumWords words := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [sumWithWork,applyWithWork_state,ih,sumWords]

def bound (count H : ℕ) : ℕ := count * (12000 * (2 * H + 2) ^ 3)

theorem sumWithWork_bound (words : List SignedWord) (hC : ∀ word ∈ words, CanonicalWord word) :
    (sumWithWork words).2 ≤ bound words.length (credit words) := by
  induction words with
  | nil => exact Nat.zero_le _
  | cons word rest ih =>
      have ht : ∀ item ∈ rest, CanonicalWord item := fun item hi => hC item (by simp [hi])
      have hHead : width word ≤ 1 + 2 * credit (word :: rest) := by have hm := credit_member (word :: rest) word (by simp); omega
      have hTail : width (sumWords rest) ≤ 1 + 2 * credit (word :: rest) :=
        (sumWords_canonical rest ht).2.trans ((rationalWordWidth_of_height (sum_height rest ht)).trans (by have hc := credit_tail word rest; omega))
      have hp := BinaryPRGPreparationWork.operation_uniform_bound .add word (sumWords rest) _ hHead hTail
      simp only [show 1 + 2 * credit (word :: rest) + 1 = 2 * credit (word :: rest) + 2 by omega] at hp
      have hr := ih ht
      have hm := Nat.mul_le_mul_left rest.length (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left
        (show 2 * credit rest + 2 ≤ 2 * credit (word :: rest) + 2 by have hc := credit_tail word rest; omega) 3))
      unfold sumWithWork
      dsimp only
      rw [sumWithWork_state]
      unfold bound at hr ⊢
      simp only [List.length_cons,Nat.add_mul,one_mul]
      omega

end Blotto.BinaryStoredWordSumWork
