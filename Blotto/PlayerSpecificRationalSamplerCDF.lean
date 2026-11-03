import Blotto.PlayerSpecificPublicRoundingCoupling
import Blotto.PlayerSpecificDownwardCDFTransport

/-! The actual public rational sampler, at its computed numerical
precisions and positive minimum, has the complete paper-level CDF bound
against the same accepted exact two-value-vector equilibrium. -/
namespace Blotto.PlayerSpecificRationalSamplerCDF
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 ∧
      ∀ player,CDFClose (PlayerSpecificFiniteSamplerLaw.law p player) (if player then accepted.lawA else accepted.lawB)
        (3*(epsilon:ℝ)/32) := by
  obtain ⟨accepted,hA,hB,hbudget,hgamma,hlength,hregA,hregB,hfield⟩ := PlayerSpecificPublicFieldLaw.accepted_CDF i epsilon p hp
  obtain ⟨x,hx,hround⟩ := PlayerSpecificPublicRoundingCoupling.original_input i epsilon p hp
  have hex : x=accepted.gamma := hgamma.2.2 x hx.1 hx.2.1
  subst x
  obtain ⟨y,hy,hminimum⟩ := PlayerSpecificFiniteSamplerContract.minimum_lower_bound i epsilon p hp
  have hey : y=accepted.gamma := hgamma.2.2 y hy.1 hy.2.1
  subst y
  have hmeta := PlayerSpecificFiniteSamplerContract.numerical_metadata i epsilon he p hp
  have hq : 0 < (p.base.minimum.quantum:ℝ) := by exact_mod_cast hmeta.2.1
  have hqe : ∀ j,(p.base.minimum.quantum:ℝ) ≤ accepted.length j := by
    intro j
    rw [←hlength j]
    exact hminimum j
  have herror : PlayerSpecificOriginalFieldCDF.error N p.accuracy.coinBits p.accuracy.scalarBits+
      (1/(2:ℝ)^p.accuracy.outputBits)/(p.base.minimum.quantum:ℝ) ≤ 3*(epsilon:ℝ)/32 := by
    have h := PlayerSpecificFiniteSamplerContract.numerical_error_budget i epsilon he p hp
    simpa only [PlayerSpecificOriginalFieldCDF.error,Nat.cast_add,Nat.cast_ofNat,add_comm,add_left_comm,add_assoc] using h
  refine ⟨accepted,hA,hB,hbudget,hregA,hregB,?_⟩
  intro player
  have hprob : ∀ j,0 ≤ (if player then accepted.probA j else accepted.probB j) ∧
      (if player then accepted.probA j else accepted.probB j) ≤ 1 := by
    intro j
    cases player
    · simpa using And.intro (accepted.probB_bounds j).1.le (accepted.probB_bounds j).2
    · simpa using And.intro (accepted.probA_bounds j).1.le (accepted.probA_bounds j).2
  have htarget : ∀ j,(marginal (if player then accepted.lawA else accepted.lawB) j : Measure ℝ)=
      zeroUniformLaw (accepted.length j) (if player then accepted.probA j else accepted.probB j) := by
    intro j
    cases player
    · simpa using accepted.lawB_marginal j
    · simpa using accepted.lawA_marginal j
  have hf := hfield player
  rw [PlayerSpecificPublicRoundingCoupling.field_law] at hf
  have h := PlayerSpecificDownwardCDFTransport.CDF_error (bitCount p)
    (PlayerSpecificPublicRoundingCoupling.fieldSample p player accepted.gamma) (PlayerSpecificFiniteSamplerLaw.sample p player)
    (if player then accepted.lawA else accepted.lawB) accepted.length (fun j => if player then accepted.probA j else accepted.probB j)
    accepted.length_pos hprob htarget (p.base.minimum.quantum:ℝ) (1/(2:ℝ)^p.accuracy.outputBits) _ hq hqe (by positivity)
    (fun bits j => (hround player bits j).1) (fun bits j => (hround player bits j).2.1)
    (fun bits j => (hround player bits j).2.2.le) hf
  exact h.mono herror

end Blotto.PlayerSpecificRationalSamplerCDF
