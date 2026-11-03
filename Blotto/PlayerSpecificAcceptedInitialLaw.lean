import Blotto.PlayerSpecificAlgebraicInitialContract

/-! The accepted exact equilibrium and the actually prepared algebraic
initial rows share the same selected root, lengths and both mixture means. -/
namespace Blotto.PlayerSpecificAcceptedInitialLaw
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
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 := by
  obtain ⟨accepted,hA,hB,hbudget,hgamma,hinterval,hscale,_,_,hregA,hregB⟩ :=
    PlayerSpecificFiniteParameterDescriptionContract.accepted_equilibrium i r hr
  obtain ⟨_,_,_,hred,x,hx,_⟩ := PlayerSpecificAlgebraicInitialContract.accepted_point i r hr
  have he : accepted.gamma=x := hx.2.2 accepted.gamma hgamma hinterval
  have hroot : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval accepted.gamma := by
    rw [he]
    exact hx
  have hs := PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hvalues := PlayerSpecificAlgebraicInitialVector.values RationalCostModel.schoolbook i r hs.1 hs.2.1 hred
    accepted.gamma hroot accepted.gamma_pos
  refine ⟨accepted,hA,hB,hbudget,hroot,hscale,?_,hregA,hregB⟩
  intro j
  have h := hvalues j
  simpa only [PlayerSpecificInput.length,PlayerSpecificInput.probA,PlayerSpecificInput.probB,hA,hB,hscale,RationalFieldSelector.values] using h

end Blotto.PlayerSpecificAcceptedInitialLaw
