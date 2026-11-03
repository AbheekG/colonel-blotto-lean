import Blotto.ProbabilityWords
import Blotto.RationalExpressionWordWidth

/-! Canonical coin words retain the probability's reduced height. Pending
fixed-denominator digits never increase that height; doubling uses one extra
bit. These statements cover deterministic endpoint coins too. -/

namespace Blotto

namespace ProbabilityWords

theorem ofRat_height (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (s : ℕ) (h : RationalHeight p s) :
    (ofRat p hp).numerator < 2 ^ s ∧ (ofRat p hp).denominator < 2 ^ s := by
  have he := Int.toNat_add_toNat_neg_eq_natAbs p.num
  exact ⟨(show p.num.toNat ≤ p.num.natAbs by omega).trans_lt h.1, h.2⟩

theorem ofRat_wordWidth (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (s : ℕ) (h : RationalHeight p s) :
    binaryWordWidth (ofRat p hp).numerator ≤ s ∧ binaryWordWidth (ofRat p hp).denominator ≤ s :=
  ⟨binaryWordWidth_le_of_lt_pow h.positive (ofRat_height p hp s h).1,
    binaryWordWidth_le_of_lt_pow h.positive (ofRat_height p hp s h).2⟩

end ProbabilityWords

theorem normalized_coin_words_height (a b s : ℕ) (hab : a ≤ b) (hb : b < 2 ^ s) :
    a < 2 ^ s ∧ b < 2 ^ s := ⟨hab.trans_lt hb, hb⟩

theorem coin_doubling_height (a s : ℕ) (ha : a < 2 ^ s) : 2 * a < 2 ^ (s + 1) := by
  rw [pow_succ]
  omega

theorem coin_residual_height (a b s : ℕ) (hab : a ≤ b) (hb : b < 2 ^ s) :
    numeratorResidual a b < 2 ^ s := (numeratorResidual_bounds a b hab).trans_lt hb

theorem coin_residual_wordWidth (a b s : ℕ) (hs : 0 < s) (hab : a ≤ b) (hb : b < 2 ^ s) :
    binaryWordWidth (numeratorResidual a b) ≤ s :=
  binaryWordWidth_le_of_lt_pow hs (coin_residual_height a b s hab hb)

theorem coin_doubling_wordWidth (a s : ℕ) (ha : a < 2 ^ s) :
    binaryWordWidth (2 * a) ≤ s + 1 :=
  binaryWordWidth_le_of_lt_pow (by omega) (coin_doubling_height a s ha)

end Blotto
