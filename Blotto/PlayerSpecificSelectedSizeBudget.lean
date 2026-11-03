import Blotto.PlayerSpecificSelectedExecution

/-! One original-input word bound covers every actual retained interval,
Sturm row, query and control along the computed selected-root path. -/
namespace Blotto.PlayerSpecificSelectedSizeBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState
open PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem endpoint_cap (m a : Data) (original : Interval) (hml : m.length≤4) (hal : a.length≤3)
    (k : ℕ) (hk : k≤PlayerSpecificSignPrecision.depth m a original) :
    3*PlayerSpecificSignEnclosure.endpointHeight original+k+2≤height (PlayerSpecificSignLinearSizes.inputHeight m a original) := by
  have hd:=PlayerSpecificSignLinearSizes.depth_linear m a original hml hal
  have he:=(PlayerSpecificSignLinearSizes.input_heights m a original).2.2.2.1
  have hcap : 3*PlayerSpecificSignEnclosure.endpointHeight original+k+2≤
      (PlayerSpecificSignLinearSizes.depthCoefficient+5)*(PlayerSpecificSignLinearSizes.inputHeight m a original+1) := by nlinarith only [hd,he,hk]
  exact hcap.trans (dominated _ _ (by unfold PlayerSpecificSignLinearSizes.depthCoefficient coefficient; omega))

theorem endpoint_heights (m a : Data) (original : Interval) (prepared : Prepared m)
    (hml : m.length≤4) (hal : a.length≤3) (node : Interval) (k : ℕ)
    (hk : k≤PlayerSpecificSignPrecision.depth m a original) (hv : Valid prepared node)
    (hg : PlayerSpecificRefinementLattice.Grid node (PlayerSpecificRefinementLattice.denominator original*2^k))
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificSignEnclosure.magnitude original:ℚ)) :
    RationalHeight node.lo (height (PlayerSpecificSignLinearSizes.inputHeight m a original)) ∧
      RationalHeight node.hi (height (PlayerSpecificSignLinearSizes.inputHeight m a original)) := by
  have hlo : |node.lo| ≤ (PlayerSpecificSignEnclosure.magnitude original:ℚ) := abs_le.mpr ⟨hb.1,hv.1.le.trans hb.2⟩
  have hhi : |node.hi| ≤ (PlayerSpecificSignEnclosure.magnitude original:ℚ) := abs_le.mpr ⟨hb.1.trans hv.1.le,hb.2⟩
  have he:=endpoint_cap m a original hml hal k hk
  exact ⟨(PlayerSpecificRefinementEndpointHeights.lattice_height node.lo _ k _
    (PlayerSpecificRefinementLattice.denominator_positive original)
    (PlayerSpecificRefinementEndpointHeights.denominator_bound original) hg.1 hlo).mono he,
    (PlayerSpecificRefinementEndpointHeights.lattice_height node.hi _ k _
    (PlayerSpecificRefinementLattice.denominator_positive original)
    (PlayerSpecificRefinementEndpointHeights.denominator_bound original) hg.2 hhi).mono he⟩

theorem rows (m a : Data) (original : Interval) (prepared : Prepared m) (hml : m.length≤4) :
    prepared.sequence.length≤5 ∧ ∀ row∈prepared.sequence,
      HasHeight row (height (PlayerSpecificSignLinearSizes.inputHeight m a original)) ∧ row.length≤4 := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a original
  have hi:=original_heights m a original
  have hp:=polynomial_heights m H hi.1 hi.2.2.2 hml
  rw [prepared.correct,←(PlayerSpecificPolynomialPreparation.values m).2.2]
  exact ⟨hp.2.2.2.2.1,hp.2.2.2.2.2⟩

theorem split_width (m a : Data) (original : Interval) (_hml : m.length≤4) :
    PlayerSpecificSplitTraceCost.width m (height (PlayerSpecificSignLinearSizes.inputHeight m a original))≤
      width (PlayerSpecificSignLinearSizes.inputHeight m a original) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a original
  have hi : PlayerSpecificRationalMagnitude.inputHeight m≤H := by unfold H PlayerSpecificSignLinearSizes.inputHeight; omega
  have hc:=PlayerSpecificSquarefreeHeights.certificate_linear (PlayerSpecificRationalMagnitude.inputHeight m)
  have hm:=Nat.mul_le_mul_left PlayerSpecificSquarefreeHeights.certificateConstant (Nat.add_le_add_right hi 1)
  have hd:=dominated PlayerSpecificSquarefreeHeights.certificateConstant H (by unfold coefficient; omega)
  have hs : PlayerSpecificSquarefreeHeights.certificateHeight (PlayerSpecificRationalMagnitude.inputHeight m)≤height H := hc.trans (hm.trans hd)
  unfold PlayerSpecificSplitTraceCost.width PlayerSpecificPreparedQueryCost.queryWidth PlayerSpecificPreparedQueryCost.queryHeight width
  change 22*(PlayerSpecificSquarefreeHeights.certificateHeight (PlayerSpecificRationalMagnitude.inputHeight m)+(2*height H+3)+1)+48+8*height H+64≤100000*(height H+1)
  omega

end Blotto.PlayerSpecificSelectedSizeBudget
