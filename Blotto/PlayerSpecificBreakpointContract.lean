import Blotto.PlayerSpecificBreakpointExecution

/-! Same-return separate breakpoint contract with all input, arithmetic,
substitution, representation and optional-result source prices joined. -/
namespace Blotto.PlayerSpecificBreakpointContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificBreakpointExecution PlayerSpecificBreakpointTestCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem frame_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H)
    (hb : RationalHeight b H) (result : Option Candidate)
    (hr : ∀ r∈result,price model (PlayerSpecificCandidateSelection.copyCandidate r)≤81*model.rat (width H)) :
    price model (frame c b result)≤400*model.rat (width H) := by
  have hw : 32≤width H := by unfold width; omega
  have hsmall : 128*(H+1)≤width H := by unfold width; omega
  have hcst:=PlayerSpecificCellTestCopyCost.cell_cost model c H hc
  have hcp:=hcst.trans (Nat.mul_le_mul_left 135 (model.monotone hsmall))
  have hbudget:=PlayerSpecificExtendedCopyCost.row_cost model [b] H (width H)
    (cons_height hb (nil_height _)) (by simp) (by unfold width; omega) hw
  have hoption:=PlayerSpecificCandidateScanCopyCost.option_cost model _ hw result hr
  have hcontrol:=event_price model (width H) (by omega) (.control (if result.isSome then 1 else 0))
    ((PlayerSpecificRationalTrace.control_width _).trans (by split <;> omega))
  change price model [.control (if result.isSome then 1 else 0)]≤3*model.rat (width H) at hcontrol
  simp only [frame,price_append]
  nlinarith only [hcp,hbudget,hoption,hcontrol]

theorem constructed_copy (model : RationalCostModel) (q : ℚ) (H : ℕ) (hq : RationalHeight q H) (hH : 1≤H) :
    price model (PlayerSpecificCandidateSelection.copyCandidate (PlayerSpecificBreakpointConstruction.run q).1)≤81*model.rat (width H) := by
  rw [PlayerSpecificBreakpointConstruction.value]
  apply PlayerSpecificCandidateSelection.copy_cost model _ (H+2) _
  · exact mono (PlayerSpecificFactorHeights.linear_height q H hq hH) (by omega)
  · simp [PlayerSpecificRationalBreakpoint.candidate,PlayerSpecificLinearFactor.linear]
  · exact (hq.sub one_height).mono (by omega)
  · exact hq.mono (by omega)
  · simp [PlayerSpecificRationalBreakpoint.candidate]
  · simp [PlayerSpecificRationalBreakpoint.candidate]
  · unfold width; omega
  · unfold width; omega

theorem source_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) :
    price model (run c b).2≤5000*model.rat (width H) := by
  have hnone:=frame_cost model c b H hc hb none (by simp)
  cases hu : c.upper with
  | none => simpa only [PlayerSpecificBreakpointExecution.run,hu] using hnone.trans (Nat.mul_le_mul_right _ (by decide : 400≤5000))
  | some q =>
    have hq:=hc.2.2.1 q (by rw [hu]; exact Option.mem_some_self _)
    have htest:=PlayerSpecificBreakpointTestCost.run_cost model c b q H hc hb hq hH
    have hconstruct:=PlayerSpecificBreakpointConstruction.run_cost model q H hq hH
    have hsmall : 128*(H+1)≤width H := by unfold width; omega
    have hconstructp:=hconstruct.trans (Nat.mul_le_mul_left 300 (model.monotone hsmall))
    have hcopy:=constructed_copy model q H hq hH
    have hsome:=frame_cost model c b H hc hb (some (PlayerSpecificBreakpointConstruction.run q).1) (by
      intro r hr
      have he : (PlayerSpecificBreakpointConstruction.run q).1=r := by
        simpa only [Option.mem_def,Option.some.injEq] using hr
      rw [←he]
      exact hcopy)
    rw [PlayerSpecificBreakpointExecution.run,hu]
    dsimp only
    split <;> simp only [price_append]
    · nlinarith only [htest,hconstructp,hsome]
    · nlinarith only [htest,hconstructp,hnone]

theorem actual_contract (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) (hb0 : b≠0) :
    (run c b).1=PlayerSpecificRationalBreakpoint.run c b ∧ price model (run c b).2≤5000*model.rat (width H) :=
  ⟨value c b hb0,source_cost model c b H hc hb hH⟩

theorem polynomial_cost (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) :
    price RationalCostModel.schoolbook (run c b).2≤(5000*(2048*2048+2048))*(H+1)^2 := by
  have hc:=source_cost RationalCostModel.schoolbook c b H hc hb hH
  change price RationalCostModel.schoolbook (run c b).2≤5000*((2048*(H+1))*(2048*(H+1))+2048*(H+1)) at hc
  have hm:=Nat.mul_le_mul_left (5000*2048) (show H+1≤(H+1)^2 by nlinarith)
  nlinarith only [hc,hm]

end Blotto.PlayerSpecificBreakpointContract
