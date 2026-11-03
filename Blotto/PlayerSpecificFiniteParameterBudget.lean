import Blotto.PlayerSpecificFiniteParameterExecution

/-! A single original-input envelope covers preparation, recognition scan,
accepted reduced scale and every final input/output/description word. -/
namespace Blotto.PlayerSpecificFiniteParameterBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 2000000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def size (N L : ℕ) : ℕ := (N+1)*(L+1)
def cellHeight (N L : ℕ) : ℕ := PlayerSpecificRecognitionInputHeights.cellHeight N L
def height (N L : ℕ) : ℕ := PlayerSpecificFiniteParameterSizes.height N L
def widthCoefficient : ℕ := 4096+PlayerSpecificRecognitionScanContract.widthCoefficient+
  11*PlayerSpecificFiniteScaleBudget.widthCoefficient+22*PlayerSpecificFiniteScaleHeights.coefficient+512
def width (N L : ℕ) : ℕ := widthCoefficient*size N L
def work (N L : ℕ) : ℕ := (N+1)^3*(L+1)
def workCoefficient : ℕ := 10000000+2*PlayerSpecificRecognitionScanContract.workCoefficient+1000000000+1000

theorem size_positive (N L : ℕ) : 1≤size N L := by
  exact Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)

theorem calibration (C N L : ℕ) (hC : C≤widthCoefficient) : C*size N L≤width N L :=
  Nat.mul_le_mul_right _ hC

theorem preparation_width (N L : ℕ) : PlayerSpecificRationalIntervalsCopyCost.width N L≤width N L := by
  have hp:=calibration 4096 N L (by unfold widthCoefficient; omega)
  dsimp only [PlayerSpecificRationalIntervalsCopyCost.width,PlayerSpecificSweepPreparationBudget.width]
  simpa only [size,mul_assoc] using hp

theorem scan_width (N L : ℕ) : PlayerSpecificRecognitionScanContract.widthCoefficient*((N+1)*(L+1))≤width N L :=
  calibration _ N L (by unfold widthCoefficient; omega)

theorem scale_width (N L : ℕ) : PlayerSpecificFiniteScaleBudget.width (cellHeight N L)≤width N L := by
  have hp:=PlayerSpecificFiniteParameterSizes.polynomial_profile PlayerSpecificFiniteScaleBudget.widthCoefficient N L
  have hc:=calibration (11*PlayerSpecificFiniteScaleBudget.widthCoefficient) N L (by unfold widthCoefficient; omega)
  exact hp.trans (by simpa only [size,mul_assoc] using hc)

theorem output_width (N L : ℕ) : 1+2*height N L≤width N L ∧ 2*N+3≤width N L ∧ 32≤width N L := by
  have hh:=PlayerSpecificFiniteParameterSizes.polynomial_height N L
  have hs:=size_positive N L
  have hm:=calibration (22*PlayerSpecificFiniteScaleHeights.coefficient+512) N L (by unfold widthCoefficient; omega)
  dsimp only [height,size] at hh hs hm ⊢
  exact ⟨by nlinarith only [hh,hm,hs],by nlinarith only [hm,hs,Nat.zero_le (N*L)],by nlinarith only [hm,hs]⟩

theorem work_profiles (N L : ℕ) : (N+1)^3≤work N L ∧
    (N+1)^2*(L+1)≤work N L ∧ N+1≤work N L ∧ 1≤work N L := by
  have hc : (N+1)^2≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have hl : N+1≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have hm:=Nat.mul_le_mul_right ((N+1)^3) (show 1≤L+1 by omega)
  have hs:=Nat.mul_le_mul_right (L+1) hc
  unfold work
  exact ⟨by simpa only [Nat.one_mul,mul_comm] using hm,hs,by nlinarith only [hm,hl],by nlinarith only [hm,hl]⟩

end Blotto.PlayerSpecificFiniteParameterBudget
