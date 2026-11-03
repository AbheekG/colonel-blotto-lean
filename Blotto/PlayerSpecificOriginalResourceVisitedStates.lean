import Blotto.PlayerSpecificResourceVisitedStates

/-! Original accepted rational inputs supply uniform row-height and
validity certificates for every resource prefix, at every finite fuel.
The certificate is proof-only and is never supplied to the sampler. -/
namespace Blotto.PlayerSpecificOriginalResourceVisitedStates
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
open PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (fuel : ℕ),PlayerSpecificResourceVisitedStates.All RationalCostModel.schoolbook p
        (fun s => Valid p x s ∧ ∀ k,HasHeight (s.data.read k)
          (PlayerSpecificAlgebraicPathContract.height N (PlayerSpecificInitialPositivePrecision.inputSize i)))
        fuel (start RationalCostModel.schoolbook p player) := by
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,_,hred,_,_,_⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hc : Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ)<r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  let H:=PlayerSpecificAlgebraicInitialInputSizes.height N (PlayerSpecificInitialPositivePrecision.inputSize i)
  have hsize:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  refine ⟨x,hx,?_⟩
  intro player fuel
  have hv : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player j) H := by
    intro j
    cases player
    · exact ⟨(hred j).2.2,(hsize j).2.2⟩
    · exact ⟨(hred j).2.1,(hsize j).2.1⟩
  have hL : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial (p.rows.read j).length ∧
      HasHeight (p.rows.read j).length H := fun j => ⟨(hred j).1,(hsize j).1⟩
  have hstart:=start_valid RationalCostModel.schoolbook p player hc.normalized hc.irreducible hc.interval x hc.root (fun j => (hv j).1)
  let c:=start_certificate RationalCostModel.schoolbook p player
  have hall : ∀ j,HasHeight ((start RationalCostModel.schoolbook p player).data.read j)
      (PlayerSpecificAlgebraicLoopHeights.storedHeight N H) := by
    intro j
    rw [start_read]
    apply mono (hv j).2
    have hHA:=PlayerSpecificAlgebraicLoopHeights.leaf_le_active N H (by have h:=j.isLt; omega)
    unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicPairHeights.resourceHeight
    omega
  apply PlayerSpecificResourceVisitedStates.of_paths
  intro k _hk choices
  have hi:=PlayerSpecificAlgebraicLoopLineage.invariant RationalCostModel.schoolbook p player x hc k
    (start RationalCostModel.schoolbook p player) choices hstart c
  have hh:=PlayerSpecificAlgebraicLoopHeights.run_heights RationalCostModel.schoolbook p player x hc k
    (start RationalCostModel.schoolbook p player) choices hstart c H hv hL hall
  exact ⟨hi.1,fun j => mono (hh j) (PlayerSpecificAlgebraicPathContract.height_profile N (PlayerSpecificInitialPositivePrecision.inputSize i))⟩

end Blotto.PlayerSpecificOriginalResourceVisitedStates
