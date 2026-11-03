import Blotto.PlayerSpecificAcceptedFieldCDF
import Blotto.PlayerSpecificFiniteSamplerLaw

/-! The actual public prepared sampler retains the same original-input
field draw and accepted equilibrium, at its computed numerical precisions. -/
namespace Blotto.PlayerSpecificPublicFieldLaw
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

noncomputable def fieldLaw {N : ℕ} (p : Prepared N) (player : Bool) (x : ℝ) : Mixed N :=
  PlayerSpecificFiniteFieldCDF.law p.base.initial p.budget player p.accuracy.coinBits p.accuracy.scalarBits x

theorem underlying {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ r,(PlayerSpecificFiniteParameterDescription.run i).parameters=some r ∧ p.budget=i.budget ∧
      p.base.initial=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r := by
  obtain ⟨base,hb,rfl⟩ := selected i epsilon p hp
  obtain ⟨r,hr,hbase⟩ := PlayerSpecificInitialMinimumContract.selected i base hb
  refine ⟨r,hr,rfl,?_⟩
  rw [hbase]
  exact PlayerSpecificInitialMinimumValues.initial_value i r

theorem accepted_CDF {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      PlayerSpecificSelectedRefinement.Unique p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval accepted.gamma ∧
      (∀ j,realEvaluate (p.base.initial.rows.read j).length accepted.gamma=accepted.length j) ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 ∧
      ∀ player,CDFClose (fieldLaw p player accepted.gamma) (if player then accepted.lawA else accepted.lawB)
        (PlayerSpecificOriginalFieldCDF.error N p.accuracy.coinBits p.accuracy.scalarBits) := by
  obtain ⟨r,hr,hbudget,hinitial⟩ := underlying i epsilon p hp
  obtain ⟨accepted,hA,hB,haccBudget,hgamma,_,hrows,hregA,hregB,hCDF⟩ := PlayerSpecificAcceptedFieldCDF.original_input i r hr
  refine ⟨accepted,hA,hB,haccBudget,?_,?_,hregA,hregB,?_⟩
  · rw [hinitial]
    exact hgamma
  · intro j
    rw [hinitial]
    exact (hrows j).1
  · intro player
    unfold fieldLaw
    rw [hinitial,hbudget]
    exact hCDF player _ _

end Blotto.PlayerSpecificPublicFieldLaw
