import Blotto.PlayerSpecificFiniteCellCopyCost

/-! Complete source price for the actual construct/generate/scan/boundary
cell search, including every cached input and returned option frame. -/
namespace Blotto.PlayerSpecificFiniteCellCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace
open PlayerSpecificFiniteCellBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total_profile (A B H R construction generation interior boundary frameA frameB : ℕ)
    (hc : construction≤1000*R) (hg : generation≤A*(H+1)*R)
    (hi : interior≤B*(H+1)*R) (hb : boundary≤5000*R)
    (hfa : frameA≤1000*R) (hfb : frameB≤1000*R) :
    construction+generation+interior+boundary+frameA+frameB≤(A+B+10000)*(H+1)*R := by
  have hm:=Nat.mul_le_mul_right (10000*R) (show 1≤H+1 by omega)
  nlinarith only [hc,hg,hi,hb,hfa,hfb,hm]

theorem caller_price_le (model : RationalCostModel) (c : Cell) (b : ℚ) :
    (PlayerSpecificFiniteCellExecution.run model c b).2≤
      price model (PlayerSpecificCubicConstruction.run c b).2+
      (PlayerSpecificCandidateExecution.run model (cubic c.state.coefficients b)).2+
      (PlayerSpecificCandidateScanExecution.run model c (PlayerSpecificFiniteCellSearch.roots model c b)).2+
      price model (PlayerSpecificBreakpointExecution.run c b).2+
      price model (PlayerSpecificFiniteCellExecution.frame c b (cubic c.state.coefficients b)
        (PlayerSpecificFiniteCellSearch.roots model c b)
        (PlayerSpecificCandidateScanExecution.run model c (PlayerSpecificFiniteCellSearch.roots model c b)).1)+
      price model (PlayerSpecificFiniteCellExecution.frame c b (cubic c.state.coefficients b)
        (PlayerSpecificFiniteCellSearch.roots model c b) (PlayerSpecificBreakpointExecution.run c b).1) := by
  simp only [PlayerSpecificFiniteCellExecution.run,PlayerSpecificCubicConstruction.value,PlayerSpecificFiniteCellSearch.roots]
  split <;> rename_i r hr <;> simp only [hr] <;> omega

theorem source_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H)
    (hp : semantics (cubic c.state.coefficients b)≠0) :
    (PlayerSpecificFiniteCellExecution.run model c b).2≤workCoefficient*(H+1)*model.rat (width H) := by
  have hw:=wide H
  have hcst:=PlayerSpecificCubicConstruction.run_cost model c b H hc hb hH
  have hcp:=hcst.trans (Nat.mul_le_mul_left 1000 (model.monotone (show 128*(H+1)≤width H by omega)))
  have hg:=generation_cost model c b H hc hb hp
  have hi:=PlayerSpecificCandidateScanContract.source_cost model c b H hc hb hH hp
  have hip:=hi.trans (Nat.mul_le_mul_left _ (model.monotone (widths H).2.1))
  have hbprice:=PlayerSpecificBreakpointContract.source_cost model c b H hc hb hH
  have hbp:=hbprice.trans (Nat.mul_le_mul_left 5000 (model.monotone (widths H).2.2))
  have hbcopy:=PlayerSpecificFiniteCellCopyCost.boundary_copy model c b H hc hH
  have hfBoundary:=PlayerSpecificFiniteCellCopyCost.frame_cost model c b H hc hb hp _ hbcopy
  have hscanCopy:=PlayerSpecificCandidateScanCopyCost.option_cost model (width H) (by omega)
    (PlayerSpecificCandidateScanExecution.run model c (PlayerSpecificFiniteCellSearch.roots model c b)).1 (by
      intro r hr
      have hmem:=PlayerSpecificCandidateScanExecution.returned_mem model c _ r hr
      have hcopy:=PlayerSpecificCandidateRecordCost.copy_cost model c b H hc hb hp r hmem
      exact hcopy.trans (Nat.mul_le_mul_left 81 (model.monotone (widths H).2.1)))
  have hfInterior:=PlayerSpecificFiniteCellCopyCost.frame_cost model c b H hc hb hp _ hscanCopy
  exact (caller_price_le model c b).trans (total_profile _ _ H _ _ _ _ _ _ _ hcp hg hip hbp hfInterior hfBoundary)

end Blotto.PlayerSpecificFiniteCellCost
