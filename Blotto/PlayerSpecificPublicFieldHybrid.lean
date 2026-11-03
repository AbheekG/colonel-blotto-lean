import Blotto.PlayerSpecificOriginalFieldHybrid
import Blotto.PlayerSpecificPublicFieldLaw

/-! The public prepared field sampler, before rational output rounding,
has the paper's exact-choice finite-midpoint hybrid at its computed K/H.
The comparison concerns complete allocations and measurable events. -/
namespace Blotto.PlayerSpecificPublicFieldHybrid
open MeasureTheory PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      PlayerSpecificSelectedRefinement.Unique p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval accepted.gamma ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 ∧
      ∀ player : Bool,∃ hybrid : Mixed N,
        PlayerSpecificEventDistance.Bound (PlayerSpecificPublicFieldLaw.fieldLaw p player accepted.gamma) hybrid
          (((N+1000:ℕ):ℝ)/(2:ℝ)^p.accuracy.coinBits) ∧
        PlayerSpecificEventDistance.distance (PlayerSpecificPublicFieldLaw.fieldLaw p player accepted.gamma) hybrid ≤
          ((N+1000:ℕ):ℝ)/(2:ℝ)^p.accuracy.coinBits ∧
        CDFClose hybrid (if player then accepted.lawA else accepted.lawB)
          (3/(2*(2:ℝ)^p.accuracy.scalarBits)) := by
  obtain ⟨r,hr,hbudget,hinitial⟩ := PlayerSpecificPublicFieldLaw.underlying i epsilon p hp
  obtain ⟨accepted,hA,hB,haccBudget,hgamma,hregA,hregB,hhybrid⟩ :=
    PlayerSpecificOriginalFieldHybrid.original_input i r hr
  refine ⟨accepted,hA,hB,haccBudget,?_,hregA,hregB,?_⟩
  · rw [hinitial]
    exact hgamma
  · intro player
    obtain ⟨hybrid,hevent,hTV,hCDF⟩ := hhybrid player p.accuracy.scalarBits
    refine ⟨hybrid,?_,?_,hCDF⟩
    · unfold PlayerSpecificPublicFieldLaw.fieldLaw
      rw [hinitial,hbudget]
      exact hevent p.accuracy.coinBits
    · unfold PlayerSpecificPublicFieldLaw.fieldLaw
      rw [hinitial,hbudget]
      exact hTV p.accuracy.coinBits

end Blotto.PlayerSpecificPublicFieldHybrid
