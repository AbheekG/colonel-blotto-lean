import Blotto.PlayerSpecificCubicConstruction

/-! Exact rational-breakpoint representation with its executed linear
factor, shifted lower endpoint, full record copies and counter tags. -/
namespace Blotto.PlayerSpecificBreakpointConstruction
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (q : ℚ) : Candidate×Trace :=
  let linear:=PlayerSpecificLinearFactorExecution.run q
  let lower:=scalar .subtract q 1
  let result:Candidate:=⟨linear.1,⟨lower.1,q,0,0⟩⟩
  (result,linear.2++lower.2++PlayerSpecificCandidateSelection.copyCandidate result++[.control 1])

theorem value (q : ℚ) : (run q).1=PlayerSpecificRationalBreakpoint.candidate q := by
  simp only [run,PlayerSpecificLinearFactorExecution.value,scalar,Arithmetic.apply,PlayerSpecificRationalBreakpoint.candidate]

theorem run_cost (model : RationalCostModel) (q : ℚ) (H : ℕ) (hq : RationalHeight q H) (hH : 1≤H) :
    price model (run q).2≤300*model.rat (128*(H+1)) := by
  have hl:=PlayerSpecificLinearFactorExecution.run_cost model q H hq hH
  have hlp:=hl.trans (Nat.mul_le_mul_left 60 (model.monotone (show 8*H+16≤128*(H+1) by omega)))
  have hsub:=price_bound model (128*(H+1)) (by omega) _
    (fits_mono (scalar_fits_height .subtract q 1 H hq (one_height.mono hH)) (by omega))
  rw [scalar_length] at hsub
  have hr : price model (PlayerSpecificCandidateSelection.copyCandidate (run q).1)≤81*model.rat (128*(H+1)) := by
    rw [value]
    apply PlayerSpecificCandidateSelection.copy_cost model _ (H+2) _
    · exact mono (PlayerSpecificFactorHeights.linear_height q H hq hH) (by omega)
    · simp [PlayerSpecificRationalBreakpoint.candidate,PlayerSpecificLinearFactor.linear]
    · exact (hq.sub one_height).mono (by omega)
    · exact hq.mono (by omega)
    · simp [PlayerSpecificRationalBreakpoint.candidate]
    · simp [PlayerSpecificRationalBreakpoint.candidate]
    · omega
    · omega
  have hcontrol:=PlayerSpecificCellTestCopyCost.control model H 1 (by decide)
  unfold PlayerSpecificCellTestCopyCost.width at hcontrol
  rw [run]
  dsimp only [run] at hr
  dsimp only
  simp only [price_append]
  nlinarith only [hlp,hsub,hr,hcontrol]

end Blotto.PlayerSpecificBreakpointConstruction
