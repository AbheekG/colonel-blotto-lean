import Blotto.Rounding
import Blotto.ProbabilityWords

/-! Computable rational pair-rounding parameters. Their real interpretation
is exactly the maintained RoundingPair, so its feasibility, progress and
expectation guarantees are retained rather than postulated anew. -/

namespace Blotto

structure RationalRoundingPair where
  lengthI : ℚ
  lengthJ : ℚ
  resourceI : ℚ
  resourceJ : ℚ
  interiorI : 0 < resourceI ∧ resourceI < lengthI
  interiorJ : 0 < resourceJ ∧ resourceJ < lengthJ

namespace RationalRoundingPair

def total (r : RationalRoundingPair) : ℚ := r.resourceI + r.resourceJ
def lower (r : RationalRoundingPair) : ℚ := max 0 (r.total - r.lengthJ)
def upper (r : RationalRoundingPair) : ℚ := min r.lengthI r.total
def probability (r : RationalRoundingPair) : ℚ := (r.resourceI - r.lower) / (r.upper - r.lower)

noncomputable def real (r : RationalRoundingPair) : RoundingPair :=
  ⟨r.lengthI, r.lengthJ, r.resourceI, r.resourceJ, by exact_mod_cast r.interiorI, by exact_mod_cast r.interiorJ⟩

theorem lower_real (r : RationalRoundingPair) : (r.lower : ℝ) = r.real.lower := by
  simp [lower, total, real, RoundingPair.lower, RoundingPair.total]

theorem upper_real (r : RationalRoundingPair) : (r.upper : ℝ) = r.real.upper := by
  simp [upper, total, real, RoundingPair.upper, RoundingPair.total]

theorem probability_real (r : RationalRoundingPair) : (r.probability : ℝ) = r.real.probability := by
  simp only [probability, Rat.cast_div, Rat.cast_sub, r.lower_real, r.upper_real]
  rfl

theorem probability_bounds (r : RationalRoundingPair) : 0 < r.probability ∧ r.probability < 1 := by
  have hp := r.real.probability_pos
  have hq := r.real.probability_lt_one
  rw [← r.probability_real] at hp hq
  exact_mod_cast (And.intro hp hq)

def words (r : RationalRoundingPair) : ProbabilityWords :=
  ProbabilityWords.ofRat r.probability ⟨le_of_lt r.probability_bounds.1, le_of_lt r.probability_bounds.2⟩

theorem words_rational (r : RationalRoundingPair) : r.words.rational = r.probability := ProbabilityWords.ofRat_rational _ _

theorem branch_feasible (r : RationalRoundingPair) {z : ℚ} (hz : z = r.lower ∨ z = r.upper) :
    0 ≤ z ∧ z ≤ r.lengthI ∧ 0 ≤ r.total - z ∧ r.total - z ≤ r.lengthJ := by
  have hzR : (z : ℝ) = r.real.lower ∨ (z : ℝ) = r.real.upper := by
    rcases hz with rfl | rfl
    · exact Or.inl r.lower_real
    · exact Or.inr r.upper_real
  have he := r.real.branch_feasible hzR
  change (0 : ℝ) ≤ z ∧ (z : ℝ) ≤ r.lengthI ∧ 0 ≤ (r.resourceI : ℝ) + r.resourceJ - z ∧
    (r.resourceI : ℝ) + r.resourceJ - z ≤ r.lengthJ at he
  dsimp [total]
  exact_mod_cast he

end RationalRoundingPair
end Blotto
