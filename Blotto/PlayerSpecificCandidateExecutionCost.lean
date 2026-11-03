import Blotto.PlayerSpecificCandidateBudget

/-! Complete original-input source cost for actual irreducible candidate
preparation, including every polynomial/root computation and retained copy. -/
namespace Blotto.PlayerSpecificCandidateExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificRationalMagnitude PlayerSpecificCandidateBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

def workCoefficient : ℕ := PlayerSpecificFactorContract.workCoefficient+PlayerSpecificRootExecutionCost.workCoefficient+14000
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem run_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificCandidateExecution.run model p).2≤workCoefficient*(inputHeight p+1)*model.rat (width p) := by
  have hW:=wide p
  have hf:=factor_bounds model p hp hlen
  have hfactor:=PlayerSpecificFactorContract.source_cost model p hp hlen
  have hfactorp:=hfactor.trans (Nat.mul_le_mul_left _ (model.monotone
    (calibrate p PlayerSpecificFactorContract.widthCoefficient (by unfold widthCoefficient; omega))))
  have hroot:=PlayerSpecificRootExecutionCost.run_cost model p hp hlen
  have hrootp:=hroot.trans (Nat.mul_le_mul_left _ (model.monotone
    (calibrate p PlayerSpecificRootExecutionCost.widthCoefficient (by unfold widthCoefficient; omega))))
  have hrows:=rows_cost model p hp hlen
  have hforest:=forest_copy model p hp hlen
  have houtput:=rows_copy model p hp hlen
  have hip:=PlayerSpecificExtendedCopyCost.row_cost model p (height p) (width p)
    (mono (input_height p) (height_input p)) (by omega) (by omega) (by omega)
  have hfp:=PlayerSpecificExtendedCopyCost.row_cost model _ (height p) (width p) hf.1 (by omega) (by omega) (by omega)
  have hsp:=PlayerSpecificExtendedCopyCost.row_cost model _ (height p) (width p) hf.2.1 (by omega) (by omega) (by omega)
  have hctrl:=event_price model (width p) (by omega) (.control 4) ((control_width 4).trans (by omega))
  change price model [.control 4]≤3*model.rat (width p) at hctrl
  rw [PlayerSpecificCandidateExecution.run]
  dsimp only
  unfold workCoefficient
  nlinarith only [hfactorp,hrootp,hrows,hforest,houtput,hip,hfp,hsp,hctrl]

theorem polynomial_cost (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificCandidateExecution.run RationalCostModel.schoolbook p).2≤polynomialCoefficient*(inputHeight p+1)^3 := by
  have hc:=run_cost RationalCostModel.schoolbook p hp hlen
  change (PlayerSpecificCandidateExecution.run RationalCostModel.schoolbook p).2≤workCoefficient*(inputHeight p+1)*
    ((widthCoefficient*(inputHeight p+1))*(widthCoefficient*(inputHeight p+1))+widthCoefficient*(inputHeight p+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificCandidateExecutionCost
