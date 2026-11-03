import Blotto.PlayerSpecificCandidateScanExecution

/-! Every frame in the at-most-three-candidate scan has a complete source
copy price, including both counters and the optional returned root. -/
namespace Blotto.PlayerSpecificCandidateScanCopyCost
open PlayerSpecificRationalCells PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificCandidateScanExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem option_cost (model : RationalCostModel) (W : ℕ) (hW : 32≤W) (result : Option Candidate)
    (h : ∀ r∈result,price model (PlayerSpecificCandidateSelection.copyCandidate r)≤81*model.rat W) :
    price model (copyOption result)≤84*model.rat W := by
  have control (n : ℕ) (hn : n≤1) : price model [.control n]≤3*model.rat W :=
    event_price model W (by omega) (.control n) ((PlayerSpecificRationalTrace.control_width n).trans (by omega))
  cases result with
  | none => exact (control 0 (by decide)).trans (Nat.mul_le_mul_right _ (by decide : 3≤84))
  | some r =>
    have hr:=h r (Option.mem_some_self r)
    have hc:=control 1 (by decide)
    simp only [copyOption,price_append]
    omega

theorem frame_cost (model : RationalCostModel) (c : Cell) (H W : ℕ) (hc : CellHeight c H)
    (hW : 128*(H+1)≤W) (rows : List Candidate) (hlen : rows.length≤3)
    (hrows : ∀ r∈rows,price model (PlayerSpecificCandidateSelection.copyCandidate r)≤81*model.rat W)
    (result : Option Candidate) (hresult : ∀ r∈result,r∈rows) :
    price model (frame c rows result)≤500*model.rat W := by
  have hw : 32≤W := by omega
  have hcprice:=PlayerSpecificCellTestCopyCost.cell_cost model c H hc
  have hcp:=hcprice.trans (Nat.mul_le_mul_left 135 (model.monotone hW))
  have hr:=PlayerSpecificCandidateRows.copy_cost model rows W hw hlen hrows
  have ho:=option_cost model W hw result (fun r hm => hrows r (hresult r hm))
  have hctrl : price model [.control rows.length,.control (if result.isSome then 1 else 0)]≤6*model.rat W := by
    have hf : Fits W [.control rows.length,.control (if result.isSome then 1 else 0)] := by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · exact (PlayerSpecificRationalTrace.control_width rows.length).trans (by omega)
      · exact (PlayerSpecificRationalTrace.control_width _).trans (by split <;> omega)
    exact price_bound model W (by omega) _ hf
  simp only [frame,price_append]
  nlinarith only [hcp,hr,ho,hctrl]

end Blotto.PlayerSpecificCandidateScanCopyCost
