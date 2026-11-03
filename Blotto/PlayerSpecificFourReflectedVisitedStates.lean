import Blotto.PlayerSpecificFourReflectedInputSourceCost
import Blotto.PlayerSpecificResourceVisitedStates

/-! All prefixes of the reflected three-resource path have a valid state
and an original-input-derived row height. The certificate is proof-only. -/
namespace Blotto.PlayerSpecificFourReflectedVisitedStates
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
open PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem all (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (x : ℝ) (T : ℕ)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Fits r.root a T) (hml : r.root.polynomial.length≤4)
    (hmT : HasHeight r.root.polynomial T) (hT : 2≤T) :
    let p:=(PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a).resources
    ∀ fuel,PlayerSpecificResourceVisitedStates.All RationalCostModel.schoolbook p
      (PlayerSpecificFiniteResourceSourceCost.StateFits p x (iterate 16 T)) fuel
      (start RationalCostModel.schoolbook p true) := by
  dsimp only
  let p:=(PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a).resources
  let model:=RationalCostModel.schoolbook
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hb:=PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T ha hm hm0 hml hmT hT
  have hmeans : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p true j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p true j) (iterate 15 T) := fun j => (hb.2.2.1 j).2
  have hlengths : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧
      HasHeight (p.rows.read j).length (iterate 15 T) := fun j => (hb.2.2.1 j).1
  have hc : Context p x := ⟨hm,hirr,hv,hx,fun j => (hlengths j).1⟩
  have hstart:=start_valid model p true hm hirr hv x hx (fun j => (hmeans j).1)
  have hall : ∀ j,HasHeight ((start model p true).data.read j)
      (PlayerSpecificAlgebraicLoopHeights.storedHeight 3 (iterate 15 T)) := by
    intro j
    rw [start_read]
    apply mono (hmeans j).2
    have hleaf:=PlayerSpecificAlgebraicLoopHeights.leaf_le_active 3 (iterate 15 T) (by omega)
    unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicPairHeights.resourceHeight
    omega
  intro fuel
  apply PlayerSpecificResourceVisitedStates.of_paths
  intro k _ choices
  have hi:=PlayerSpecificAlgebraicLoopLineage.invariant model p true x hc k
    (start model p true) choices hstart (start_certificate model p true)
  have hh:=PlayerSpecificAlgebraicLoopHeights.run_heights model p true x hc k
    (start model p true) choices hstart (start_certificate model p true)
    (iterate 15 T) hmeans hlengths hall
  exact ⟨hi.1,fun j => mono (hh j) (by
    change PlayerSpecificAlgebraicLoopHeights.storedHeight 3 (iterate 15 T)≤step (iterate 15 T)
    exact PlayerSpecificAlgebraicFourReflectedSizes.stored_height_le (iterate 15 T))⟩

end Blotto.PlayerSpecificFourReflectedVisitedStates
