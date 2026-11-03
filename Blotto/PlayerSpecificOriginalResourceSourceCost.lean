import Blotto.PlayerSpecificResourceVisitedTransfer
import Blotto.PlayerSpecificAlgebraicFiniteDrawHeights

/-! Accepted rational inputs derive the complete resource-loop source
bound at their actual cached state, root and fixed fair-bit block list. -/
namespace Blotto.PlayerSpecificOriginalResourceSourceCost
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (N L H : ℕ) : ℕ := PlayerSpecificAlgebraicFiniteDrawContract.base N L+N+H+1
def work (N L H : ℕ) : ℕ := (N+1)*PlayerSpecificFiniteResourceSourceCost.coefficient*
  (PlayerSpecificResourceStepSizes.height (size N L H)+1)^3

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      (PlayerSpecificFiniteResourceExecution.run RationalCostModel.schoolbook p H (N-1)
        (start RationalCostModel.schoolbook p player) (PlayerSpecificFiniteResourceLoop.blocks (N-1) H bits)).2≤
          work N (PlayerSpecificInitialPositivePrecision.inputSize i) H := by
  dsimp only
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,hvisited⟩:=PlayerSpecificOriginalResourceVisitedStates.original_input i r hr
  obtain ⟨z,hz,_,hred,_,_,_⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hez : z=x := hx.2.2 z hz.1 hz.2.1
  subst z
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hroot:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hlength:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  have hc : Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ)<r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  intro player H bits
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let U:=size N L H
  have hFU : PlayerSpecificFiniteParameterSizes.height N L≤U := by dsimp [U,size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hIU : PlayerSpecificAlgebraicInitialInputSizes.height N L≤U := by dsimp [U,size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hRU : PlayerSpecificAlgebraicPathContract.height N L≤U := by dsimp [U,size,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hN : N≤U := by dsimp [U,size]; omega
  have hH : H≤U := by dsimp [U,size]; omega
  have hm : HasHeight p.parameters.root.polynomial U := mono hroot.1 hFU
  have he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U :=
    cons_height (hroot.2.1.mono hFU) (cons_height (hroot.2.2.1.mono hFU) (nil_height _))
  have hl : ∀ j,HasHeight (p.rows.read j).length U := fun j => mono (hlength j).1 hIU
  have hAll : PlayerSpecificResourceVisitedStates.All RationalCostModel.schoolbook p
      (PlayerSpecificFiniteResourceSourceCost.StateFits p x U) (N-1) (start RationalCostModel.schoolbook p player) := by
    apply PlayerSpecificResourceVisitedTransfer.mono RationalCostModel.schoolbook p _ _ _ (N-1)
      (start RationalCostModel.schoolbook p player) (hvisited player (N-1))
    intro s hstate
    exact ⟨hstate.1,fun j => mono (hstate.2 j) hRU⟩
  have hcost:=PlayerSpecificFiniteResourceSourceCost.cost p x hc U hN hs.2.2.1 hm he hl H hH (N-1)
    (start RationalCostModel.schoolbook p player) (PlayerSpecificFiniteResourceLoop.blocks (N-1) H bits) (by omega)
      (by rw [PlayerSpecificFiniteResourceLoop.blocks_length]; omega) hAll
  exact hcost.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show N-1+1≤N+1 by omega)))

end Blotto.PlayerSpecificOriginalResourceSourceCost
