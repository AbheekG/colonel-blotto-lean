import Blotto.PlayerSpecificFiniteCellExecution

/-! One original-cell width covers root generation, the exact interior
scan, rational breakpoint, all record copies and the enclosing caller. -/
namespace Blotto.PlayerSpecificFiniteCellBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells PlayerSpecificRationalCellHeights
set_option autoImplicit false
set_option maxHeartbeats 2000000

def widthCoefficient : ℕ := 17*PlayerSpecificCandidateBudget.widthCoefficient+
  PlayerSpecificCandidateScanContract.widthCoefficient+2048
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)
def workCoefficient : ℕ := 17*PlayerSpecificCandidateExecutionCost.workCoefficient+
  PlayerSpecificCandidateScanContract.workCoefficient+10000
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem cubic_size (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H) :
    PlayerSpecificRationalMagnitude.inputHeight (cubic c.state.coefficients b)+1≤17*(H+1) := by
  have he:=PlayerSpecificCellPolynomialHeights.cubic_encoding c b H hc hb
  omega

theorem root_profile (C S H : ℕ) (hS : S+1≤17*(H+1)) : C*(S+1)≤(17*C)*(H+1) := by
  calc
    _ ≤ C*(17*(H+1)) := Nat.mul_le_mul_left C hS
    _ = _ := by ring

theorem widths (H : ℕ) :
    (17*PlayerSpecificCandidateBudget.widthCoefficient)*(H+1)≤width H ∧
      PlayerSpecificCandidateScanContract.widthCoefficient*(H+1)≤width H ∧
      2048*(H+1)≤width H := by
  exact ⟨Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega),
    Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega),
    Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)⟩

theorem wide (H : ℕ) : 8*PlayerSpecificCellCandidateHeights.height H+128*(H+1)≤width H :=
  (PlayerSpecificCandidateRecordCost.wide H).trans (widths H).2.1

theorem generation_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hp : semantics (cubic c.state.coefficients b)≠0) :
    (PlayerSpecificCandidateExecution.run model (cubic c.state.coefficients b)).2≤
      (17*PlayerSpecificCandidateExecutionCost.workCoefficient)*(H+1)*model.rat (width H) := by
  have hi:=cubic_size c b H hc hb
  have hs:=PlayerSpecificCandidateExecutionCost.run_cost model _ hp (by rfl)
  have hw:=root_profile PlayerSpecificCandidateBudget.widthCoefficient _ H hi
  have hwork:=root_profile PlayerSpecificCandidateExecutionCost.workCoefficient _ H hi
  exact hs.trans (Nat.mul_le_mul hwork (model.monotone (hw.trans (widths H).1)))

end Blotto.PlayerSpecificFiniteCellBudget
