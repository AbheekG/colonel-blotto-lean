import Blotto.PlayerSpecificRationalSamplerCDF
import Blotto.ProductSamplerStability

/-! The actual public rational finite-bit sampler is an epsilon-Nash
profile in the continuous hard-budget game with separate value rows.
All probability and numerical choices are those computed by prepare. -/
namespace Blotto.PlayerSpecificFiniteSamplerNash
open MeasureTheory PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem regrets {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    regret i.valuesA.values 1 (PlayerSpecificFiniteSamplerLaw.law p true) (PlayerSpecificFiniteSamplerLaw.law p false) ≤ (epsilon:ℝ) ∧
      regret i.valuesB.values (i.budget:ℝ) (PlayerSpecificFiniteSamplerLaw.law p false) (PlayerSpecificFiniteSamplerLaw.law p true) ≤ (epsilon:ℝ) := by
  obtain ⟨accepted,_,_,_,hregA,hregB,hCDF⟩ := PlayerSpecificRationalSamplerCDF.original_input i epsilon he p hp
  have hA : CDFClose (PlayerSpecificFiniteSamplerLaw.law p true) accepted.lawA (3*(epsilon:ℝ)/32) := by simpa using hCDF true
  have hB : CDFClose (PlayerSpecificFiniteSamplerLaw.law p false) accepted.lawB (3*(epsilon:ℝ)/32) := by simpa using hCDF false
  have hs := both_regrets_stability i.valuesA.values i.valuesB.values (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ (i.budget:ℝ) by exact_mod_cast i.budget_pos.le) hA.symm hB.symm
  rw [hregA,hregB] at hs
  have heps : (0:ℝ) < epsilon := by exact_mod_cast he
  exact ⟨by nlinarith only [hs.1,heps],by nlinarith only [hs.2,heps]⟩

theorem actual_contract {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    Supported 1 (PlayerSpecificFiniteSamplerLaw.law p true) ∧
      Supported (i.budget:ℝ) (PlayerSpecificFiniteSamplerLaw.law p false) ∧
      regret i.valuesA.values 1 (PlayerSpecificFiniteSamplerLaw.law p true) (PlayerSpecificFiniteSamplerLaw.law p false) ≤ (epsilon:ℝ) ∧
      regret i.valuesB.values (i.budget:ℝ) (PlayerSpecificFiniteSamplerLaw.law p false) (PlayerSpecificFiniteSamplerLaw.law p true) ≤ (epsilon:ℝ) ∧
      (PlayerSpecificFiniteSamplerLaw.joint p : Measure (Allocation N × Allocation N))=
        (PlayerSpecificFiniteSamplerLaw.law p true : Measure (Allocation N)).prod
          (PlayerSpecificFiniteSamplerLaw.law p false : Measure (Allocation N)) := by
  have hbudgetA : Supported 1 (PlayerSpecificFiniteSamplerLaw.law p true) := by
    simpa using PlayerSpecificFiniteSamplerLaw.supported i epsilon p hp true
  have hbudgetB : Supported (i.budget:ℝ) (PlayerSpecificFiniteSamplerLaw.law p false) := by
    simpa using PlayerSpecificFiniteSamplerLaw.supported i epsilon p hp false
  have hreg := regrets i epsilon he p hp
  exact ⟨hbudgetA,hbudgetB,hreg.1,hreg.2,PlayerSpecificFiniteSamplerLaw.joint_product p⟩

theorem continuous_deviations {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    (∀ y : Allocation N,Blotto.Feasible 1 y →
      purePayoff i.valuesA.values y (PlayerSpecificFiniteSamplerLaw.law p false) ≤
        expected i.valuesA.values (PlayerSpecificFiniteSamplerLaw.law p true) (PlayerSpecificFiniteSamplerLaw.law p false)+(epsilon:ℝ)) ∧
    (∀ y : Allocation N,Blotto.Feasible (i.budget:ℝ) y →
      purePayoff i.valuesB.values y (PlayerSpecificFiniteSamplerLaw.law p true) ≤
        expected i.valuesB.values (PlayerSpecificFiniteSamplerLaw.law p false) (PlayerSpecificFiniteSamplerLaw.law p true)+(epsilon:ℝ)) := by
  have hreg := regrets i epsilon he p hp
  constructor
  · intro y hy
    have h := purePayoff_le_security i.valuesA.values hy (PlayerSpecificFiniteSamplerLaw.law p false)
    unfold regret at hreg
    linarith only [h,hreg.1]
  · intro y hy
    have h := purePayoff_le_security i.valuesB.values hy (PlayerSpecificFiniteSamplerLaw.law p true)
    unfold regret at hreg
    linarith only [h,hreg.2]

end Blotto.PlayerSpecificFiniteSamplerNash
