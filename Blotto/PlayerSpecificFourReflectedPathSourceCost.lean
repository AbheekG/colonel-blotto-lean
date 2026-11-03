import Blotto.PlayerSpecificFourReflectedPathExecution
import Blotto.PlayerSpecificFiniteResourceEntryCost
import Blotto.PlayerSpecificResourceVisitedTransfer

/-! Original four-input source price for the complete measured reflected
resource path, including initial state, finite fair blocks, loop and return. -/
namespace Blotto.PlayerSpecificFourReflectedPathSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (T H : ℕ) : ℕ := iterate 16 T+H+3
def work (T H : ℕ) : ℕ :=
  PlayerSpecificFourReflectedInputSourceCost.work T+
  4*PlayerSpecificResourceEntryPriceProfile.startCoefficient*(size T H+1)^3+
  PlayerSpecificResourceBlockPolynomial.coefficient*3^3*(H+1)^3+
  3*PlayerSpecificFiniteResourceSourceCost.coefficient*(PlayerSpecificResourceStepSizes.height (size T H)+1)^3+
  PlayerSpecificFiniteResourceSourceCost.frameCoefficient*(PlayerSpecificResourceStepSizes.height (size T H)+1)^3+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (x : ℝ) (T H : ℕ)
    (bits : Fin (2*H) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Fits r.root a T) (hml : r.root.polynomial.length≤4)
    (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T) :
    (PlayerSpecificFourReflectedPathExecution.run r a H bits).2≤work T H := by
  let model:=RationalCostModel.schoolbook
  let p:=(PlayerSpecificAlgebraicFourReflectedInput.prepare model r a).resources
  let U:=size T H
  let initial:=PlayerSpecificAlgebraicStateExecution.start model p true
  let blocks:=PlayerSpecificResourceBlockExecution.blocks model 2 H bits
  let result:=PlayerSpecificFiniteResourceExecution.run model p H 2 initial.1 blocks.1
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hb:=PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T ha hm hm0 hml hmT hT
  have h16:=PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
  have h1516:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15≤16)
  have hTU : T≤U := by dsimp only [U,size]; omega
  have h15U : iterate 15 T≤U := h1516.trans (by dsimp only [U,size]; omega)
  have h16U : iterate 16 T≤U := by dsimp only [U,size]; omega
  have hNU : 3≤U := by dsimp only [U,size]; omega
  have hHU : H≤U := by dsimp only [U,size]; omega
  have hU : 1≤U := by omega
  have hmean : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p true j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p true j) U := by
    intro j
    exact ⟨(hb.2.2.1 j).2.1,mono (hb.2.2.1 j).2.2 h15U⟩
  have hl : ∀ j,HasHeight (p.rows.read j).length U := fun j => mono (hb.2.2.1 j).1.2 h15U
  have hc : Context p x := ⟨hm,hirr,hv,hx,fun j => (hb.2.2.1 j).1.1⟩
  have hAll16:=PlayerSpecificFourReflectedVisitedStates.all r a x T hm hirr hv hx ha hml hmT hT 2
  have hAll : PlayerSpecificResourceVisitedStates.All model p
      (PlayerSpecificFiniteResourceSourceCost.StateFits p x U) 2 (start model p true) :=
    PlayerSpecificResourceVisitedTransfer.mono model p _ _
      (fun s hs => ⟨hs.1,fun j => mono (hs.2 j) h16U⟩) 2 (start model p true) hAll16
  have hinput:=PlayerSpecificFourReflectedInputSourceCost.cost r a T hm hm0 hml hmT he hv hT ha
  have hstart:=PlayerSpecificResourceEntryPriceProfile.start_cost p true x hc U hNU hU hml
    (mono hmT hTU) (mono he hTU) hl hmean
  have hblocks:=PlayerSpecificResourceBlockPolynomial.cost 2 H bits
  have hblockLen : blocks.1.length=2 := PlayerSpecificResourceBlockExecution.blocks_length model 2 H bits
  have hloop : result.2≤3*PlayerSpecificFiniteResourceSourceCost.coefficient*
      (PlayerSpecificResourceStepSizes.height U+1)^3 := by
    dsimp only [result]
    rw [PlayerSpecificAlgebraicStateExecution.start_value,PlayerSpecificResourceBlockExecution.blocks_value]
    have hgeneric:=PlayerSpecificFiniteResourceSourceCost.cost p x hc U hNU hml (mono hmT hTU)
      (mono he hTU) hl H hHU
    have hbNative : (PlayerSpecificFiniteResourceLoop.blocks 2 H bits).length≤U := by
      rw [PlayerSpecificFiniteResourceLoop.blocks_length]
      omega
    have hbound:=hgeneric 2 (start model p true) (PlayerSpecificFiniteResourceLoop.blocks 2 H bits)
      (by omega) hbNative hAll
    exact hbound
  have hreturn : PlayerSpecificFiniteResourceSourceCost.StateFits p x U result.1.1 := by
    dsimp only [result]
    rw [PlayerSpecificAlgebraicStateExecution.start_value]
    exact PlayerSpecificResourceVisitedStates.measured_output model p _ H 2 (start model p true) hAll blocks.1
  have hvisits : result.1.2≤2 := PlayerSpecificFiniteResourceExecution.visits_le model p H 2 initial.1 blocks.1
  have hframe:=PlayerSpecificFiniteResourceSourceCost.frame_cost p result.1.1 x U hreturn hNU H 2
    blocks.1.length result.1.2 hHU (by omega) (by rw [hblockLen]; omega) (hvisits.trans (by omega))
    hml (mono hmT hTU) (mono he hTU) hl hc.lengths
  have hentry : (PlayerSpecificFiniteResourceEntryExecution.draw p true H bits).2≤
      4*PlayerSpecificResourceEntryPriceProfile.startCoefficient*(U+1)^3+
      PlayerSpecificResourceBlockPolynomial.coefficient*3^3*(H+1)^3+
      3*PlayerSpecificFiniteResourceSourceCost.coefficient*(PlayerSpecificResourceStepSizes.height U+1)^3+
      PlayerSpecificFiniteResourceSourceCost.frameCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
    change initial.2+blocks.2+result.2+
      PlayerSpecificFiniteResourceExecution.frame model p H 2 blocks.1.length result.1.2 result.1.1≤_
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hstart hblocks) hloop) hframe
  rw [PlayerSpecificFourReflectedPathExecution.price_equation]
  have hshape : work T H = PlayerSpecificFourReflectedInputSourceCost.work T+
      (4*PlayerSpecificResourceEntryPriceProfile.startCoefficient*(U+1)^3+
       PlayerSpecificResourceBlockPolynomial.coefficient*3^3*(H+1)^3+
       3*PlayerSpecificFiniteResourceSourceCost.coefficient*(PlayerSpecificResourceStepSizes.height U+1)^3+
       PlayerSpecificFiniteResourceSourceCost.frameCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3)+2 := by
    dsimp only [U]
    simp only [work,Nat.add_assoc]
  rw [hshape]
  exact Nat.add_le_add_right (Nat.add_le_add hinput hentry) 2

end Blotto.PlayerSpecificFourReflectedPathSourceCost
