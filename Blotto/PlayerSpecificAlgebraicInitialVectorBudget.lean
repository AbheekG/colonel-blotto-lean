import Blotto.PlayerSpecificAlgebraicInitialVectorExecution

/-! One original-input envelope covers field operations, the shared
inverse, measured native indices and copies of all initial coefficients. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVectorBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def size (N L : ℕ) : ℕ := (N+1)*(L+1)
def baseCoefficient : ℕ := 11*PlayerSpecificFiniteScaleHeights.coefficient+4
def widthCoefficient : ℕ := PlayerSpecificAlgebraicInitialOriginalCost.widthCoefficient+
  PlayerSpecificAlgebraicInverseContract.widthCoefficient*baseCoefficient+
  2*PlayerSpecificAlgebraicInitialOriginalCost.heightCoefficient+256
def width (N L : ℕ) : ℕ := widthCoefficient*size N L
def callbackCoefficient : ℕ := PlayerSpecificAlgebraicInitialOriginalCost.workCoefficient+1000
def workCoefficient : ℕ := callbackCoefficient+8000000000
def address (N : ℕ) : ℕ := PlayerSpecificBitRatioSortExecution.address RationalCostModel.schoolbook
  (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).1

theorem size_bounds (N L : ℕ) : 1≤size N L ∧ N+1≤size N L ∧ L+1≤size N L ∧ N+L+1≤size N L := by
  unfold size
  have h:=Nat.zero_le (N*L)
  constructor
  · exact Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)
  · exact ⟨by nlinarith only [h],by nlinarith only [h],by nlinarith only [h]⟩

theorem base_bound (N L : ℕ) : PlayerSpecificAlgebraicInitialInputSizes.base N L+1≤baseCoefficient*size N L := by
  have hf:=PlayerSpecificFiniteParameterSizes.polynomial_height N L
  have hs:=size_bounds N L
  unfold PlayerSpecificAlgebraicInitialInputSizes.base baseCoefficient size at *
  nlinarith only [hf,hs.1,hs.2.2.1]

theorem field_width (N L : ℕ) : PlayerSpecificAlgebraicInitialOriginalCost.widthCoefficient*size N L≤width N L :=
  Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

theorem input_width (N L : ℕ) : PlayerSpecificBitRatioSortBudget.width N L≤width N L := by
  have hs:=(size_bounds N L).2.2.2
  have hc:=Nat.mul_le_mul_right (size N L) (show 128≤widthCoefficient by unfold widthCoefficient; omega)
  unfold PlayerSpecificBitRatioSortBudget.width width
  nlinarith only [hs,hc]

theorem inverse_width (N L : ℕ) :
    PlayerSpecificAlgebraicInverseExecution.width (PlayerSpecificAlgebraicInitialInputSizes.base N L)≤width N L := by
  have hi:=PlayerSpecificAlgebraicInverseContract.width_linear (PlayerSpecificAlgebraicInitialInputSizes.base N L)
  have hb:=Nat.mul_le_mul_left PlayerSpecificAlgebraicInverseContract.widthCoefficient (base_bound N L)
  have hc:=Nat.mul_le_mul_right (size N L) (show PlayerSpecificAlgebraicInverseContract.widthCoefficient*baseCoefficient≤widthCoefficient by
    unfold widthCoefficient; omega)
  unfold width
  nlinarith only [hi,hb,hc]

theorem copy_width (N L : ℕ) :
    1+2*PlayerSpecificAlgebraicInitialInputSizes.height N L≤width N L ∧ 32≤width N L ∧ N+1≤width N L := by
  have hg:=PlayerSpecificAlgebraicInitialOriginalCost.height_polynomial N L
  have hs:=size_bounds N L
  have hc:=Nat.mul_le_mul_right (size N L) (show 2*PlayerSpecificAlgebraicInitialOriginalCost.heightCoefficient+256≤widthCoefficient by
    unfold widthCoefficient; omega)
  unfold width
  dsimp only [PlayerSpecificAlgebraicInitialOriginalCost.size] at hg
  dsimp only [size] at hs hc ⊢
  exact ⟨by nlinarith only [hg,hc],by nlinarith only [hc,hs.1,Nat.zero_le (PlayerSpecificAlgebraicInitialOriginalCost.heightCoefficient*((N+1)*(L+1)))],
    by nlinarith only [hc,hs.2.1,Nat.zero_le (PlayerSpecificAlgebraicInitialOriginalCost.heightCoefficient*((N+1)*(L+1)))]⟩

theorem input_le_height (N L : ℕ) : L≤PlayerSpecificAlgebraicInitialInputSizes.height N L := by
  have hb:=PlayerSpecificInitialPositivePrecision.base_le_height (PlayerSpecificAlgebraicInitialInputSizes.base N L)
  have hL : L≤PlayerSpecificAlgebraicInitialInputSizes.base N L := by unfold PlayerSpecificAlgebraicInitialInputSizes.base; omega
  exact hL.trans hb

theorem address_bounds (N L : ℕ) : 1≤address N ∧ address N≤64*RationalCostModel.schoolbook.rat (width N L) ∧
    ∀ j≤N,RationalCostModel.schoolbook.rat (binaryWordWidth (j+1))≤address N := by
  have h:=PlayerSpecificBitRatioSortBudget.measured_bounds RationalCostModel.schoolbook N L
  exact ⟨h.1,h.2.1.trans (Nat.mul_le_mul_left 64 (RationalCostModel.schoolbook.monotone (input_width N L))),h.2.2⟩

end Blotto.PlayerSpecificAlgebraicInitialVectorBudget
