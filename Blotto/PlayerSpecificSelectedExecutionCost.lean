import Blotto.PlayerSpecificSelectedTraceCost

/-! Complete depth-bounded actual selected-root refinement source cost.
The proof follows the general rational lattice at every live prefix. -/
namespace Blotto.PlayerSpecificSelectedExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem denominator_add (D k f : ℕ) : (D*2^k)*2^f=D*2^(k+f) := by rw [pow_add]; ring

theorem final_grid {m : Data} (prepared : Prepared m) (fuel : ℕ) (node : Interval) (D k : ℕ)
    (hD : 0<D) (hg : PlayerSpecificRefinementLattice.Grid node (D*2^k)) :
    PlayerSpecificRefinementLattice.Grid (PlayerSpecificSelectedRefinement.run prepared fuel node) (D*2^(k+fuel)) := by
  have hp : 0<D*2^k := Nat.mul_pos hD (Nat.two_pow_pos _)
  simpa only [denominator_add] using PlayerSpecificRefinementLattice.run_grid prepared fuel node (D*2^k) hp hg

theorem next_grid {m : Data} (prepared : Prepared m) (node : Interval) (D k : ℕ)
    (hD : 0<D) (hg : PlayerSpecificRefinementLattice.Grid node (D*2^k)) :
    PlayerSpecificRefinementLattice.Grid (PlayerSpecificSelectedRefinement.step prepared node) (D*2^(k+1)) := by
  have hp : 0<D*2^k := Nat.mul_pos hD (Nat.two_pow_pos _)
  simpa only [show (D*2^k)*2=D*2^(k+1) by rw [pow_succ]; ring] using
    PlayerSpecificRefinementLattice.step_grid prepared node (D*2^k) hp hg

theorem run_cost (model : RationalCostModel) (m a : Data) (original : Interval) (prepared : Prepared m)
    (hml : m.length≤4) (hal : a.length≤3) (fuel : ℕ) (node : Interval) (k : ℕ)
    (hcap : k+fuel≤PlayerSpecificSignPrecision.depth m a original) (hn : Valid prepared node)
    (hg : PlayerSpecificRefinementLattice.Grid node (PlayerSpecificRefinementLattice.denominator original*2^k))
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificSignEnclosure.magnitude original:ℚ)) :
    (PlayerSpecificSelectedExecution.run model prepared fuel node).2≤
      6000*(fuel+1)*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a original)) := by
  induction fuel generalizing node k with
  | zero =>
    have hk : k≤PlayerSpecificSignPrecision.depth m a original := by omega
    have he:=PlayerSpecificSelectedSizeBudget.endpoint_heights m a original prepared hml hal node k hk hn hg hb
    have hf:=PlayerSpecificSelectedTraceCost.frame_cost model m a original prepared hml 0 node node hn hn he.1 he.2 he.1 he.2 (by omega)
    change price model (PlayerSpecificSelectedExecution.frame prepared 0 node node)≤_
    exact hf.trans (Nat.mul_le_mul_right _ (by decide : 150≤6000*(0+1)))
  | succ fuel ih =>
    let chosen:=PlayerSpecificSelectedRefinement.step prepared node
    have hc : Valid prepared chosen := PlayerSpecificSelectedRefinement.step_valid prepared node hn
    have hcg : PlayerSpecificRefinementLattice.Grid chosen (PlayerSpecificRefinementLattice.denominator original*2^(k+1)) :=
      next_grid prepared node _ k (PlayerSpecificRefinementLattice.denominator_positive original) hg
    have hcb : PlayerSpecificDyadicEndpoints.Bounded chosen (PlayerSpecificSignEnclosure.magnitude original:ℚ) :=
      PlayerSpecificRefinementEndpointHeights.step_bounded prepared node _ hn hb
    have hi:=ih chosen (k+1) (by omega) hc hcg hcb
    have hnheights:=PlayerSpecificSelectedSizeBudget.endpoint_heights m a original prepared hml hal node k (by omega) hn hg hb
    have hrvalid:=PlayerSpecificSelectedRefinement.run_valid prepared fuel chosen hc
    have hrgrid:=final_grid prepared fuel chosen _ (k+1) (PlayerSpecificRefinementLattice.denominator_positive original) hcg
    have hrbound:=PlayerSpecificRefinementEndpointHeights.run_bounded prepared fuel chosen _ hc hcb
    have hrheights:=PlayerSpecificSelectedSizeBudget.endpoint_heights m a original prepared hml hal
      (PlayerSpecificSelectedRefinement.run prepared fuel chosen) (k+1+fuel) (by omega) hrvalid hrgrid hrbound
    have hdepth:=PlayerSpecificSelectedSizeBudget.endpoint_cap m a original hml hal
      (PlayerSpecificSignPrecision.depth m a original) (le_refl _)
    have hframe:=PlayerSpecificSelectedTraceCost.frame_cost model m a original prepared hml (fuel+1) node
      (PlayerSpecificSelectedRefinement.run prepared fuel chosen) hn hrvalid
      hnheights.1 hnheights.2 hrheights.1 hrheights.2 (by omega)
    have hsplit:=PlayerSpecificSelectedTraceCost.split_cost model m a original prepared hml node hn hnheights.1 hnheights.2
    rw [PlayerSpecificSelectedExecution.run]
    dsimp only
    simp only [PlayerSpecificSplitExecution.value]
    change price model (PlayerSpecificSplitExecution.run prepared node).2+
      (PlayerSpecificSelectedExecution.run model prepared fuel chosen).2+
      price model (PlayerSpecificSelectedExecution.frame prepared (fuel+1) node
        (PlayerSpecificSelectedExecution.run model prepared fuel chosen).1)≤_
    rw [PlayerSpecificSelectedExecution.value]
    nlinarith only [hi,hsplit,hframe]

end Blotto.PlayerSpecificSelectedExecutionCost
