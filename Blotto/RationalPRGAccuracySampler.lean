import Blotto.RationalPRGFiniteNash
import Blotto.RationalAccuracyPrecision

/-! Rational accuracy input selects the bounded draw precision directly.
The actual finite whole laws satisfy both continuous Nash bounds at ε. -/

namespace Blotto.RationalPRGInput

def richApproximateSample {n : ℕ} (i : RationalPRGInput n) (ε : ℚ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) : Fin n → ℚ :=
  i.richSample (rationalAccuracyPrecision ε) bits

def poorApproximateSample {n : ℕ} (i : RationalPRGInput n) (ε : ℚ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) : Fin n → ℚ :=
  i.poorSample (rationalAccuracyPrecision ε) bits

theorem rational_accuracy_regrets {n : ℕ} (i : RationalPRGInput n) (ε : ℚ) (hε : 0 < ε) :
    regret i.real.values 1 (i.richSampleLaw (rationalAccuracyPrecision ε)) (i.poorSampleLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) ∧
      regret i.real.values (i.b : ℝ) (i.poorSampleLaw (rationalAccuracyPrecision ε)) (i.richSampleLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) :=
  i.sample_epsilon (by exact_mod_cast hε) (rationalAccuracyPrecision_real_guard ε hε)

theorem richApproximateSample_fullBudget {n : ℕ} (i : RationalPRGInput n) (ε : ℚ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) :
    FullBudget 1 (fun j => (i.richApproximateSample ε bits j : ℝ)) := i.richSample_fullBudget _ bits

theorem poorApproximateSample_fullBudget {n : ℕ} (i : RationalPRGInput n) (ε : ℚ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) :
    FullBudget (i.b : ℝ) (fun j => (i.poorApproximateSample ε bits j : ℝ)) := i.poorSample_fullBudget _ bits

end Blotto.RationalPRGInput
