import Blotto.PlayerSpecificRecognitionScanExecution

/-! Original cell-list length and coefficient heights bound every source
word in the full recognition scan. These are analysis bounds, not runtime
parameters or arithmetic/cost oracles. -/
namespace Blotto.PlayerSpecificRecognitionScanBudget
set_option autoImplicit false
set_option maxHeartbeats 1500000

def widthCoefficient : ℕ := PlayerSpecificFiniteCellBudget.widthCoefficient+128
def width (N H : ℕ) : ℕ := widthCoefficient*(N+H+1)
def cellWork (H : ℕ) : ℕ := PlayerSpecificFiniteCellBudget.workCoefficient*(H+1)
def unitWork (N H : ℕ) : ℕ := 2*cellWork H+500*(N+1)

theorem widths (N H : ℕ) : PlayerSpecificFiniteCellBudget.width H≤width N H ∧
    128*(H+1)≤width N H ∧ N+1≤width N H ∧ 32≤width N H := by
  have hs : H+1≤N+H+1 := by omega
  have hcell:=Nat.mul_le_mul (show PlayerSpecificFiniteCellBudget.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega) hs
  have hbase:=Nat.mul_le_mul_right (N+H+1) (show 128≤widthCoefficient by unfold widthCoefficient; omega)
  refine ⟨hcell,?_,?_,?_⟩ <;> unfold width at * <;> omega

theorem frame_profile (T E R F : ℕ) (hF : F≤T*R+E*R) : T*R+F≤(2*T+E)*R := by nlinarith only [hF]

end Blotto.PlayerSpecificRecognitionScanBudget
