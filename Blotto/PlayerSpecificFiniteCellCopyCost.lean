import Blotto.PlayerSpecificFiniteCellBudget

/-! Full cell caller frames price both accepted representations and every
cached candidate. Optional rational-boundary returns derive their own
complete copy bounds from the executed degree-one constructor. -/
namespace Blotto.PlayerSpecificFiniteCellCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificFiniteCellBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem rows_copy (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hp : semantics (cubic c.state.coefficients b)≠0) :
    price model (PlayerSpecificCandidateRows.copyRows (PlayerSpecificFiniteCellSearch.roots model c b))≤250*model.rat (width H) := by
  have hw:=wide H
  apply PlayerSpecificCandidateRows.copy_cost model _ (width H) (by omega)
    (PlayerSpecificCandidateContract.actual_contract model _ hp (by rfl)).1
  intro r hr
  exact (PlayerSpecificCandidateRecordCost.copy_cost model c b H hc hb hp r hr).trans
    (Nat.mul_le_mul_left 81 (model.monotone (widths H).2.1))

theorem boundary_copy (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hH : 1≤H) :
    price model (PlayerSpecificCandidateScanExecution.copyOption (PlayerSpecificBreakpointExecution.run c b).1)≤84*model.rat (width H) := by
  have hw:=wide H
  apply PlayerSpecificCandidateScanCopyCost.option_cost model _ (by omega)
  intro r hr
  cases hu : c.upper with
  | none => simp only [PlayerSpecificBreakpointExecution.run,hu,Option.not_mem_none] at hr
  | some q =>
    have hq:=hc.2.2.1 q (by rw [hu]; exact Option.mem_some_self _)
    have hcopy:=PlayerSpecificBreakpointContract.constructed_copy model q H hq hH
    have hcopyp:=hcopy.trans (Nat.mul_le_mul_left 81 (model.monotone (widths H).2.2))
    simp only [PlayerSpecificBreakpointExecution.run,hu] at hr
    split at hr
    · have he : (PlayerSpecificBreakpointConstruction.run q).1=r := by
        simpa only [Option.mem_def,Option.some.injEq] using hr
      rw [←he]
      exact hcopyp
    · simp only [Option.not_mem_none] at hr

theorem frame_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hp : semantics (cubic c.state.coefficients b)≠0)
    (result : Option Candidate)
    (hresult : price model (PlayerSpecificCandidateScanExecution.copyOption result)≤84*model.rat (width H)) :
    price model (PlayerSpecificFiniteCellExecution.frame c b (cubic c.state.coefficients b)
      (PlayerSpecificFiniteCellSearch.roots model c b) result)≤1000*model.rat (width H) := by
  have hw:=wide H
  have hsmall : 128*(H+1)≤width H := by omega
  have hcc:=PlayerSpecificCellTestCopyCost.cell_cost model c H hc
  have hccp:=hcc.trans (Nat.mul_le_mul_left 135 (model.monotone hsmall))
  have hbc:=PlayerSpecificExtendedCopyCost.row_cost model [b] H (width H)
    (cons_height hb (nil_height _)) (by simp) (by omega) (by omega)
  have hpc:=PlayerSpecificExtendedCopyCost.row_cost model (cubic c.state.coefficients b) (2*H) (width H)
    (PlayerSpecificCellPolynomialHeights.cubic_height c b H hc hb) (by simp [cubic]) (by omega) (by omega)
  have hrows:=rows_copy model c b H hc hb hp
  have hlen : (PlayerSpecificFiniteCellSearch.roots model c b).length≤3 :=
    (PlayerSpecificCandidateContract.actual_contract model _ hp (by rfl)).1
  have hcontrol:=event_price model (width H) (by omega) (.control (PlayerSpecificFiniteCellSearch.roots model c b).length)
    ((PlayerSpecificRationalTrace.control_width _).trans (by omega))
  change price model [.control (PlayerSpecificFiniteCellSearch.roots model c b).length]≤3*model.rat (width H) at hcontrol
  simp only [PlayerSpecificFiniteCellExecution.frame,price_append]
  nlinarith only [hccp,hbc,hpc,hrows,hresult,hcontrol]

end Blotto.PlayerSpecificFiniteCellCopyCost
