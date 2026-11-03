import Blotto.PlayerSpecificFiniteResourceEntryExecution

/-! The measured resource entry derives every root, row, initial mean
and reached-state certificate from the accepted original rational input. -/
namespace Blotto.PlayerSpecificResourceEntryInput
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (N L : ℕ) : ℕ := PlayerSpecificOriginalResourceSourceCost.size N L 0

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    let T:=height N (PlayerSpecificInitialPositivePrecision.inputSize i)
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧ Context p x ∧
      p.parameters.root.polynomial.length≤4 ∧ HasHeight p.parameters.root.polynomial T ∧
      HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T ∧
      (∀ j,HasHeight (p.rows.read j).length T) ∧
      (∀ (player : Bool) j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player j) ∧
        HasHeight (PlayerSpecificInitialLineageBound.means p player j) T) ∧
      (∀ (player : Bool) (fuel : ℕ),PlayerSpecificResourceVisitedStates.All RationalCostModel.schoolbook p
        (PlayerSpecificFiniteResourceSourceCost.StateFits p x T) fuel (start RationalCostModel.schoolbook p player)) := by
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let T:=height N L
  obtain ⟨x,hx,hvisited⟩:=PlayerSpecificOriginalResourceVisitedStates.original_input i r hr
  obtain ⟨z,hz,_,hred,_,_,_⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hez : z=x := hx.2.2 z hz.1 hz.2.1
  subst z
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hroot:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hrows:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  have hFT : PlayerSpecificFiniteParameterSizes.height N L≤T := by
    dsimp [T,height,PlayerSpecificOriginalResourceSourceCost.size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hIT : PlayerSpecificAlgebraicInitialInputSizes.height N L≤T := by
    dsimp [T,height,PlayerSpecificOriginalResourceSourceCost.size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hRT : PlayerSpecificAlgebraicPathContract.height N L≤T := by
    dsimp [T,height,PlayerSpecificOriginalResourceSourceCost.size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hc : Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ)<r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  refine ⟨x,hx,hc,hs.2.2.1,mono hroot.1 hFT,?_,fun j => mono (hrows j).1 hIT,?_,?_⟩
  · exact cons_height (hroot.2.1.mono hFT) (cons_height (hroot.2.2.1.mono hFT) (nil_height _))
  · intro player j
    cases player
    · exact ⟨(hred j).2.2,mono (hrows j).2.2 hIT⟩
    · exact ⟨(hred j).2.1,mono (hrows j).2.1 hIT⟩
  · intro player fuel
    apply PlayerSpecificResourceVisitedTransfer.mono RationalCostModel.schoolbook p _ _ _ fuel
      (start RationalCostModel.schoolbook p player) (hvisited player fuel)
    intro s hstate
    exact ⟨hstate.1,fun j => mono (hstate.2 j) hRT⟩

theorem size_lower (N L : ℕ) : N≤height N L ∧ 1≤height N L := by
  unfold height PlayerSpecificOriginalResourceSourceCost.size
  omega

end Blotto.PlayerSpecificResourceEntryInput
