import Blotto.PlayerSpecificCellConstructionExecution

/-! All cell-construction input/state/suffix and returned-list copies at
the actual additive sweep heights. -/
namespace Blotto.PlayerSpecificCellConstructionCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalSweepHeights PlayerSpecificSweep PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (T H N : ℕ) : ℕ := bound T H N
def width (T H N : ℕ) : ℕ := PlayerSpecificSweepTraceFits.width (height T H N) (N+2)

theorem large (T H N : ℕ) : T≤height T H N ∧ H≤height T H N ∧
    stepBound T H≤height T H N ∧ 128*(height T H N+1)≤width T H N ∧ N+3≤width T H N := by
  have hm:=Nat.mul_le_mul_left (3*H+1) (show 1≤N+1 by omega)
  unfold width PlayerSpecificSweepTraceFits.width height bound stepBound at *
  omega

theorem cells_copy (model : RationalCostModel) (cells : List Cell) (B W : ℕ) (hc : ∀ c∈cells,CellHeight c B)
    (hBW : 128*(B+1)≤W) (hlen : cells.length+1≤W) :
    price model (PlayerSpecificRecognitionScanExecution.copyCells cells)≤(135*cells.length+3)*model.rat W := by
  have hW : 6≤W := by omega
  have hs : (cells.map (fun c => price model (PlayerSpecificCellTestConstruction.copyCell c))).sum≤cells.length*(135*model.rat W) := by
    induction cells with
    | nil => simp
    | cons c cs ih =>
      have hh:=PlayerSpecificCellTestCopyCost.cell_cost model c B (hc c List.mem_cons_self)
      have hhp:=hh.trans (Nat.mul_le_mul_left 135 (model.monotone hBW))
      have ht:=ih (fun d hd => hc d (List.mem_cons_of_mem c hd)) (by simp only [List.length_cons] at hlen; omega)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hhp,ht]
  have hctrl:=event_price model W (by omega) (.control cells.length)
    ((PlayerSpecificRationalTrace.control_width _).trans hlen)
  change price model [.control cells.length]≤3*model.rat W at hctrl
  rw [PlayerSpecificRecognitionScanExecution.copyCells,price_append,PlayerSpecificTraversalPrice.price_flatMap]
  nlinarith only [hs,hctrl]

theorem frame_cost (model : RationalCostModel) (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows)
    (T H : ℕ) (hs : StateHeight s T) (hl : RationalHeight lower T)
    (hx : PlayerSpecificSuffixCost.RowsHeight xs H) :
    price model (PlayerSpecificCellConstructionExecution.frame s lower xs
      (PlayerSpecificCellConstructionExecution.run model s lower xs).1)≤500*(xs.length+2)*model.rat (width T H xs.length) := by
  let B:=height T H xs.length
  let W:=width T H xs.length
  have hw:=large T H xs.length
  have hBW : 1+2*B≤W := by dsimp only [B,W]; omega
  have hW : 6≤W := by dsimp only [W]; omega
  have hstate:=price_bound model W (by omega) _
    (PlayerSpecificSweepTraceFits.copy_state_fits s B W (state_mono s T B hs hw.1) hBW hW)
  rw [PlayerSpecificSweepExecution.copy_state_length] at hstate
  have hlow:=price_bound model W (by omega) _ (copyRow_fits W [lower]
    (fun q hq => (rationalWordWidth_of_height ((cons_height (hl.mono hw.1) (nil_height _)) q hq)).trans hBW) (by simp; omega))
  rw [copyRow_length] at hlow
  have hrows:=price_bound model W (by omega) _
    (PlayerSpecificSuffixCost.copy_fits xs B W (fun x hm =>
      ⟨(hx x hm).1.mono hw.2.1,(hx x hm).2.1.mono hw.2.1,(hx x hm).2.2.mono hw.2.1⟩)
      hBW (by dsimp only [W]; omega) (by omega))
  rw [PlayerSpecificSuffixExecution.copy_rows_length] at hrows
  have hcells : ∀ c∈(PlayerSpecificCellConstructionExecution.run model s lower xs).1,CellHeight c B := by
    rw [PlayerSpecificCellConstructionExecution.value]
    exact build_height s lower xs T H hs hl hx
  have hlen:=PlayerSpecificCellConstructionExecution.length model s lower xs
  have houtput:=cells_copy model _ B W hcells hw.2.2.2.1 (by rw [hlen]; dsimp only [W]; omega)
  have hcontrol : Fits W [.control xs.length,.control (PlayerSpecificCellConstructionExecution.run model s lower xs).1.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by dsimp only [W]; omega)
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by rw [hlen]; dsimp only [W]; omega)
  have hpctrl:=price_bound model W (by omega) _ hcontrol
  rw [hlen] at houtput
  simp only [List.length_cons,List.length_nil] at hlow hpctrl
  simp only [PlayerSpecificCellConstructionExecution.frame,price_append]
  nlinarith only [hstate,hlow,hrows,houtput,hpctrl]

end Blotto.PlayerSpecificCellConstructionCopyCost
