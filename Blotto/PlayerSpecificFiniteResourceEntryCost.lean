import Blotto.PlayerSpecificResourceEntryPriceProfile

/-! The complete actual resource entry has one original-input polynomial
source bound: initial state, fair-block offsets/materialization, adaptive
loop and returned caller state are all included on its native return. -/
namespace Blotto.PlayerSpecificFiniteResourceEntryCost
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      (PlayerSpecificFiniteResourceEntryExecution.draw p player H bits).2≤
        PlayerSpecificResourceEntryPriceProfile.coefficient*(N+1)^7*(PlayerSpecificInitialPositivePrecision.inputSize i+H+1)^3 := by
  dsimp only
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  let model:=RationalCostModel.schoolbook
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let T:=PlayerSpecificResourceEntryInput.height N L
  obtain ⟨x,_hx,hc,hml,hm,he,hl,hmean,hvisited⟩:=PlayerSpecificResourceEntryInput.original_input i r hr
  have hNT : N≤T := (PlayerSpecificResourceEntryInput.size_lower N L).1
  have hT : 1≤T := (PlayerSpecificResourceEntryInput.size_lower N L).2
  intro player H bits
  let S:=PlayerSpecificOriginalResourceSourceCost.size N L H
  let D:=PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1
  let A:=L+H+1
  let initial:=PlayerSpecificAlgebraicStateExecution.start model p player
  let blocks:=PlayerSpecificResourceBlockExecution.blocks model (N-1) H bits
  let result:=PlayerSpecificFiniteResourceExecution.run model p H (N-1) initial.1 blocks.1
  have hTS : T≤S := by dsimp [T,PlayerSpecificResourceEntryInput.height,S,PlayerSpecificOriginalResourceSourceCost.size]; omega
  have hNS : N≤S := hNT.trans hTS
  have hS : 1≤S := hT.trans hTS
  have hHS : H≤S := by dsimp [S,PlayerSpecificOriginalResourceSourceCost.size]; omega
  have hsize : S+1≤D*(N+1)^2*A := PlayerSpecificResourceSourcePolynomial.size_bound N L H
  have hstart:=PlayerSpecificResourceEntryPriceProfile.start_cost p player x hc T hNT hT hml hm he hl (hmean player)
  have hstartQ : initial.2≤(PlayerSpecificResourceEntryPriceProfile.startCoefficient*D^3)*(N+1)^7*A^3 :=
    hstart.trans (PlayerSpecificResourceEntryPriceProfile.transfer _ D N A T ((Nat.add_le_add_right hTS 1).trans hsize))
  have hblocks:=PlayerSpecificResourceBlockPolynomial.cost (N-1) H bits
  have hblocksQ : blocks.2≤PlayerSpecificResourceBlockPolynomial.coefficient*(N+1)^7*A^3 :=
    hblocks.trans (PlayerSpecificResourceEntryPriceProfile.block_transfer N L H)
  have hloopQ : result.2≤PlayerSpecificResourceSourcePolynomial.coefficient*(N+1)^7*A^3 := by
    change (PlayerSpecificFiniteResourceExecution.run model p H (N-1)
      (PlayerSpecificAlgebraicStateExecution.start model p player).1
      (PlayerSpecificResourceBlockExecution.blocks model (N-1) H bits).1).2≤_
    rw [PlayerSpecificAlgebraicStateExecution.start_value,PlayerSpecificResourceBlockExecution.blocks_value]
    exact PlayerSpecificResourceSourcePolynomial.original_input i r hr player H bits
  have hreturnT : PlayerSpecificFiniteResourceSourceCost.StateFits p x T result.1.1 := by
    change PlayerSpecificFiniteResourceSourceCost.StateFits p x T
      (PlayerSpecificFiniteResourceExecution.run model p H (N-1)
        (PlayerSpecificAlgebraicStateExecution.start model p player).1 blocks.1).1.1
    rw [PlayerSpecificAlgebraicStateExecution.start_value]
    exact PlayerSpecificResourceVisitedStates.measured_output model p _ H (N-1)
      (start model p player) (hvisited player (N-1)) blocks.1
  have hreturnS : PlayerSpecificFiniteResourceSourceCost.StateFits p x S result.1.1 :=
    ⟨hreturnT.1,fun j => mono (hreturnT.2 j) hTS⟩
  have hvisits : result.1.2≤N-1 := PlayerSpecificFiniteResourceExecution.visits_le model p H (N-1) initial.1 blocks.1
  have hblockLen : blocks.1.length=N-1 := PlayerSpecificResourceBlockExecution.blocks_length model (N-1) H bits
  have hframe:=PlayerSpecificResourceEntryPriceProfile.frame_cost p result.1.1 x hc S hreturnS hNS hS H (N-1)
    blocks.1.length result.1.2 hHS (by omega) (by rw [hblockLen]; omega) (by omega) hml
      (mono hm hTS) (mono he hTS) (fun j => mono (hl j) hTS)
  have hframeN : PlayerSpecificResourceEntryPriceProfile.frameCoefficient*(S+1)^3≤
      (N+1)*PlayerSpecificResourceEntryPriceProfile.frameCoefficient*(S+1)^3 := by
    have hp:=Nat.mul_le_mul_right (PlayerSpecificResourceEntryPriceProfile.frameCoefficient*(S+1)^3) (show 1≤N+1 by omega)
    simpa only [Nat.one_mul,Nat.mul_assoc] using hp
  have hframeQ : PlayerSpecificFiniteResourceExecution.frame model p H (N-1) blocks.1.length result.1.2 result.1.1≤
      (PlayerSpecificResourceEntryPriceProfile.frameCoefficient*D^3)*(N+1)^7*A^3 :=
    (hframe.trans hframeN).trans (PlayerSpecificResourceEntryPriceProfile.transfer _ D N A S hsize)
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hstartQ hblocksQ) hloopQ) hframeQ
  change initial.2+blocks.2+result.2+
    PlayerSpecificFiniteResourceExecution.frame model p H (N-1) blocks.1.length result.1.2 result.1.1≤_
  apply hsum.trans_eq
  change _=((PlayerSpecificResourceEntryPriceProfile.startCoefficient+PlayerSpecificResourceEntryPriceProfile.frameCoefficient)*D^3+
    PlayerSpecificResourceBlockPolynomial.coefficient+PlayerSpecificResourceSourcePolynomial.coefficient)*(N+1)^7*A^3
  ring

theorem same_return_and_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      (PlayerSpecificFiniteResourceEntryExecution.draw p player H bits).1=PlayerSpecificFiniteResourceLoop.draw p player H bits ∧
      (PlayerSpecificFiniteResourceEntryExecution.draw p player H bits).2≤
        PlayerSpecificResourceEntryPriceProfile.coefficient*(N+1)^7*(PlayerSpecificInitialPositivePrecision.inputSize i+H+1)^3 := by
  dsimp only
  intro player H bits
  exact ⟨PlayerSpecificFiniteResourceEntryExecution.value _ player H bits,original_input i r hr player H bits⟩

end Blotto.PlayerSpecificFiniteResourceEntryCost
