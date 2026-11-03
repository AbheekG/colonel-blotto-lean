import Blotto.ProductSamplerStability

/-! Independent finite player seeds push forward to the product of their
whole-allocation laws. This preserves within-row dependence and supports the
canonical continuous-deviation regret transfer, never a correlated equilibrium. -/

namespace Blotto
open MeasureTheory

theorem independent_seed_pair_law {n : ℕ} (R S : ℕ)
    (sampleA : (Fin R → Bool) → Allocation n) (sampleB : (Fin S → Bool) → Allocation n) :
    Measure.map (Prod.map sampleA sampleB)
      ((fairBitLaw R : Measure (Fin R → Bool)).prod (fairBitLaw S : Measure (Fin S → Bool))) =
      (Measure.map sampleA (fairBitLaw R : Measure (Fin R → Bool))).prod
        (Measure.map sampleB (fairBitLaw S : Measure (Fin S → Bool))) :=
  (Measure.map_prod_map _ _ (measurable_of_countable sampleA) (measurable_of_countable sampleB)).symm

theorem sampled_profile_regrets {n : ℕ} (values : Values n) {A B targetError deltaA deltaB : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (targetA targetB sampleA sampleB : Mixed n)
    (hTargetA : Supported A targetA) (hTargetB : Supported B targetB)
    (hTarget : security values A targetB + security values B targetA ≤ 1 + targetError)
    (hCDF_A : CDFClose sampleA targetA deltaA) (hCDF_B : CDFClose sampleB targetB deltaB) :
    regret values A sampleA sampleB ≤ targetError + deltaA + 2 * deltaB ∧
      regret values B sampleB sampleA ≤ targetError + deltaB + 2 * deltaA := by
  have hRegret := regrets_le_of_security_sum values targetA targetB hTargetA hTargetB hTarget
  have hStable := productSampler_regret_stability values values hA hB
    targetA targetB sampleA sampleB hCDF_A hCDF_B
  constructor <;> linarith [hRegret.1, hRegret.2, hStable.1, hStable.2]

end Blotto
