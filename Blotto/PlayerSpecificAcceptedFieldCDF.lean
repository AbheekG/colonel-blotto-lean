import Blotto.PlayerSpecificOriginalFieldCDF
import Blotto.PlayerSpecificFixedRootInputUnique

/-! One accepted exact input simultaneously carries the actual initial
row refinement, retained scale, exact regrets and complete field CDF bound. -/
namespace Blotto.PlayerSpecificAcceptedFieldCDF
open MeasureTheory PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval accepted.gamma ∧
      accepted.scale=realEvaluate r.scale accepted.gamma ∧
      (∀ j,realEvaluate (p.rows.read j).length accepted.gamma=accepted.length j ∧
        realEvaluate (p.rows.read j).initialA accepted.gamma=accepted.probA j*accepted.length j ∧
        realEvaluate (p.rows.read j).initialB accepted.gamma=accepted.probB j*accepted.length j) ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 ∧
      ∀ (player : Bool) (H K : ℕ),CDFClose (PlayerSpecificFiniteFieldCDF.law p i.budget player H K accepted.gamma)
        (if player then accepted.lawA else accepted.lawB) (PlayerSpecificOriginalFieldCDF.error N H K) := by
  obtain ⟨a,haA,haB,habudget,hga,hregA,hregB,hCDF⟩ := PlayerSpecificOriginalFieldCDF.original_input i r hr
  obtain ⟨b,hbA,hbB,hbbudget,hgb,hscale,hrows,_,_⟩ := PlayerSpecificAcceptedInitialLaw.original_input i r hr
  have hg : a.gamma=b.gamma := hgb.2.2 a.gamma hga.1 hga.2.1
  have he : a=b := PlayerSpecificFixedRootInputUnique.eq_of_values_root a b (haA.trans hbA.symm) (haB.trans hbB.symm)
    (habudget.trans hbbudget.symm) hg
  subst a
  exact ⟨b,hbA,hbB,hbbudget,hgb,hscale,hrows,hregA,hregB,hCDF⟩

end Blotto.PlayerSpecificAcceptedFieldCDF
