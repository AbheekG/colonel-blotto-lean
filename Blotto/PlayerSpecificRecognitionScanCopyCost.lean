import Blotto.PlayerSpecificRecognitionScanBudget

/-! Every full recognition frame copies its actual cell list, returned
cell/root, budget and control words. The selected-root copy is bounded
through the executed cell caller's own complete return-copy price. -/
namespace Blotto.PlayerSpecificRecognitionScanCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificRecognitionScanExecution PlayerSpecificRecognitionScanBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem control_cost (model : RationalCostModel) (N H n : ℕ) (hn : n≤N+1) :
    price model [.control n]≤3*model.rat (width N H) := by
  have hw:=widths N H
  exact event_price model _ (by omega) (.control n)
    ((PlayerSpecificRationalTrace.control_width n).trans (by
      have hm:=Nat.mul_le_mul_right (N+H+1) (show 128≤widthCoefficient by unfold widthCoefficient; omega)
      unfold width at *
      omega))

theorem cell_copy (model : RationalCostModel) (c : Cell) (N H : ℕ) (hc : CellHeight c H) :
    price model (PlayerSpecificCellTestConstruction.copyCell c)≤135*model.rat (width N H) :=
  (PlayerSpecificCellTestCopyCost.cell_cost model c H hc).trans
    (Nat.mul_le_mul_left 135 (model.monotone (widths N H).2.1))

theorem cells_copy (model : RationalCostModel) (cells : List Cell) (N H : ℕ) (hlen : cells.length≤N)
    (hc : ∀ c∈cells,CellHeight c H) :
    price model (copyCells cells)≤(135*cells.length+3)*model.rat (width N H) := by
  have hs : (cells.map (fun c => price model (PlayerSpecificCellTestConstruction.copyCell c))).sum≤
      cells.length*(135*model.rat (width N H)) := by
    induction cells with
    | nil => simp
    | cons c cs ih =>
      have hh:=cell_copy model c N H (hc c List.mem_cons_self)
      have ht:=ih (by simp only [List.length_cons] at hlen; omega)
        (fun d hd => hc d (List.mem_cons_of_mem c hd))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hh,ht]
  have hctrl:=control_cost model N H cells.length (by omega)
  rw [copyCells,price_append,PlayerSpecificTraversalPrice.price_flatMap]
  nlinarith only [hs,hctrl]

theorem result_copy (model : RationalCostModel) (b : ℚ) (cells : List Cell) (N H : ℕ)
    (hc : ∀ c∈cells,CellHeight c H)
    (htest : ∀ c∈cells,(PlayerSpecificFiniteCellExecution.run model c b).2≤cellWork H*model.rat (width N H))
    (result : Option (Cell×Candidate))
    (hr : ∀ c r,result=some (c,r) → c∈cells ∧ (PlayerSpecificFiniteCellExecution.run model c b).1=some r) :
    price model (copyResult result)≤cellWork H*model.rat (width N H)+138*model.rat (width N H) := by
  cases result with
  | none =>
    have hctrl:=control_cost model N H 0 (by omega)
    exact hctrl.trans (by omega)
  | some pair =>
    obtain ⟨c,r⟩:=pair
    have hret:=hr c r rfl
    have hcell:=cell_copy model c N H (hc c hret.1)
    have hcopy:=PlayerSpecificFiniteCellHandover.returned_copy_le model c b
    rw [hret.2] at hcopy
    simp only [PlayerSpecificCandidateScanExecution.copyOption,price_append] at hcopy
    have htestc:=htest c hret.1
    have hctrl:=control_cost model N H 1 (by omega)
    simp only [copyResult,price_append]
    nlinarith only [hcell,hcopy,htestc,hctrl]

theorem frame_cost (model : RationalCostModel) (b : ℚ) (cells : List Cell) (N H : ℕ)
    (hb : RationalHeight b H) (hlen : cells.length≤N) (hc : ∀ c∈cells,CellHeight c H)
    (htest : ∀ c∈cells,(PlayerSpecificFiniteCellExecution.run model c b).2≤cellWork H*model.rat (width N H))
    (result : Option (Cell×Candidate))
    (hr : ∀ c r,result=some (c,r) → c∈cells ∧ (PlayerSpecificFiniteCellExecution.run model c b).1=some r) :
    price model (frame b cells result)≤cellWork H*model.rat (width N H)+500*(N+1)*model.rat (width N H) := by
  have hw:=widths N H
  have hcells:=cells_copy model cells N H hlen hc
  have hresult:=result_copy model b cells N H hc htest result hr
  have hbudget:=PlayerSpecificExtendedCopyCost.row_cost model [b] H (width N H)
    (cons_height hb (nil_height _)) (by simp) (by omega) hw.2.2.2
  have hn:=control_cost model N H cells.length (by omega)
  have htag:=control_cost model N H (if result.isSome then 1 else 0) (by split <;> omega)
  have hcontrols : price model [.control cells.length,.control (if result.isSome then 1 else 0)]≤6*model.rat (width N H) := by
    change price model ([.control cells.length]++[.control (if result.isSome then 1 else 0)])≤_
    rw [price_append]
    omega
  have hm:=Nat.mul_le_mul_right (135*model.rat (width N H)) hlen
  simp only [frame,price_append]
  nlinarith only [hcells,hresult,hbudget,hcontrols,hm]

end Blotto.PlayerSpecificRecognitionScanCopyCost
