import Blotto.RationalPRGFiniteSampler
import Blotto.RationalLottoIdealLaw
import Blotto.PRGApproximation

/-! The actual native bounded fair-bit PRG programs have the final marginal
CDF bounds and both Nash guarantees against all continuous at-most deviations.
This closes their probability/feasibility linkage, separately from cost/encoding. -/

namespace Blotto.RationalPRGInput
open MeasureTheory

theorem richSampleLaw_CDF_error {n : ℕ} (i : RationalPRGInput n) (K : ℕ) :
    CDFClose (i.richSampleLaw K) i.real.richLaw (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := i.richNativeSystem.paperSampleLaw_CDF_error K
  rw [i.richNativeSystem_real] at h
  exact h

theorem poorSampleLaw_CDF_error {n : ℕ} (i : RationalPRGInput n) (K : ℕ) :
    CDFClose (i.poorSampleLaw K) i.real.poorLaw (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := i.poorNativeSystem.paperSampleLaw_CDF_error K
  rw [i.poorNativeSystem_real] at h
  exact h

theorem richSampleLaw_supported {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : Supported 1 (i.richSampleLaw K) :=
  (i.richSampleLaw_fullBudget K).mono (fun _ hx => ⟨hx.1, le_of_eq hx.2⟩)

theorem poorSampleLaw_supported {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : Supported (i.b : ℝ) (i.poorSampleLaw K) :=
  (i.poorSampleLaw_fullBudget K).mono (fun _ hx => ⟨hx.1, le_of_eq hx.2⟩)

theorem sample_regrets {n : ℕ} (i : RationalPRGInput n) (K : ℕ) :
    regret i.real.values 1 (i.richSampleLaw K) (i.poorSampleLaw K) ≤ 5 / (2 : ℝ) ^ K ∧
      regret i.real.values (i.b : ℝ) (i.poorSampleLaw K) (i.richSampleLaw K) ≤ 5 / (2 : ℝ) ^ K := by
  have h := i.real.approximation_regrets (i.richSampleLaw K) (i.poorSampleLaw K)
    (i.richSampleLaw_supported K) (i.poorSampleLaw_supported K)
    (i.richSampleLaw_CDF_error K).symm (i.poorSampleLaw_CDF_error K).symm
  have hsum : 5 / (2 * (2 : ℝ) ^ K) + 5 / (2 * (2 : ℝ) ^ K) = 5 / (2 : ℝ) ^ K := by field_simp; ring
  rw [hsum] at h
  exact h

theorem sample_epsilon {n : ℕ} (i : RationalPRGInput n) {ε : ℝ} (hε : 0 < ε) {K : ℕ}
    (hK : 32 ≤ ε * (2 : ℝ) ^ K) :
    regret i.real.values 1 (i.richSampleLaw K) (i.poorSampleLaw K) < ε ∧
      regret i.real.values (i.b : ℝ) (i.poorSampleLaw K) (i.richSampleLaw K) < ε :=
  prg_epsilon_of_distances i.real hε hK _ _ (i.richSampleLaw_supported K) (i.poorSampleLaw_supported K)
    (i.richSampleLaw_CDF_error K).symm (i.poorSampleLaw_CDF_error K).symm

end Blotto.RationalPRGInput
