import Blotto.PlayerSpecificResourceDiscrepancy

/-! Original accepted rational inputs yield the adaptive resource error
bound for the actual flat fair-bit program, uniformly over both players
and arbitrary bounded functions of the complete reached state. -/
namespace Blotto.PlayerSpecificOriginalResourceDiscrepancy
open MeasureTheory
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H : ℕ) (f : State N → ℝ), (∀ t,0 ≤ f t ∧ f t ≤ 1) →
        |(∫ bits,f (PlayerSpecificFiniteResourceLoop.draw p player H bits).1
            ∂(fairBitLaw ((N-1)*H) : Measure (Fin ((N-1)*H) → Bool)))-
          PlayerSpecificResourceIdealMean.mean RationalCostModel.schoolbook p x f (N-1) (start RationalCostModel.schoolbook p player)| ≤
            ((N-1:ℕ):ℝ)/(2:ℝ)^H := by
  let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,_,hred,hbox,hA,hB⟩ := PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hs := PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hc : PlayerSpecificAlgebraicResourceLoop.Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ) < r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  refine ⟨x,hx,?_⟩
  intro player H f hf
  have hmeans : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial
      (PlayerSpecificInitialLineageBound.means p player j) := by
    intro j
    cases player
    · exact (hred j).2.2
    · exact (hred j).2.1
  have hstart := start_valid RationalCostModel.schoolbook p player hc.normalized hc.irreducible hc.interval x hc.root hmeans
  exact PlayerSpecificResourceDiscrepancy.actual_valid RationalCostModel.schoolbook p x hc H (N-1)
    (start RationalCostModel.schoolbook p player) hstart f hf

end Blotto.PlayerSpecificOriginalResourceDiscrepancy
