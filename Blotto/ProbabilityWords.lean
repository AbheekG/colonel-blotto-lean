import Blotto.WordStateMachine

/-! Exact extraction of fixed-denominator coin words from a normalized
rational probability. This uses the stored numerator/denominator, without
searching for a rational representation of a real expression. -/

namespace Blotto

structure ProbabilityWords where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  normalized : numerator ≤ denominator

namespace ProbabilityWords

def rational (w : ProbabilityWords) : ℚ := (w.numerator : ℚ) / w.denominator

theorem nonnegative_numerator_cast (p : ℚ) (hp : 0 ≤ p) : (p.num.toNat : ℚ) = (p.num : ℚ) := by
  exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hp)

def ofRat (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : ProbabilityWords where
  numerator := p.num.toNat
  denominator := p.den
  denominator_pos := p.den_pos
  normalized := by
    have hb : (0 : ℚ) < p.den := by exact_mod_cast p.den_pos
    have he : (p.num : ℚ) ≤ p.den := by
      have hl := hp.2
      rw [← p.num_div_den, div_le_one hb] at hl
      exact hl
    have hn : (p.num.toNat : ℚ) ≤ p.den := by rw [nonnegative_numerator_cast p hp.1]; exact he
    exact_mod_cast hn

theorem ofRat_rational (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : (ofRat p hp).rational = p := by
  change (p.num.toNat : ℚ) / p.den = p
  rw [nonnegative_numerator_cast p hp.1, p.num_div_den]

end ProbabilityWords
end Blotto
