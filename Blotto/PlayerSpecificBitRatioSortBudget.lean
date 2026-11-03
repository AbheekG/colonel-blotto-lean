import Blotto.PlayerSpecificBitRatioSortExecution

/-! Actual measured sort/index words and original rational operand sizes
give one polynomial input envelope; no word-length primitive is assumed. -/
namespace Blotto.PlayerSpecificBitRatioSortBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificBitRatioSortExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (N H : ℕ) : ℕ := 128*(N+H+1)

theorem measured_bounds (model : RationalCostModel) (N H : ℕ) :
    1≤address model (PlayerSpecificWidthExecution.run model (N+1)).1 ∧
      address model (PlayerSpecificWidthExecution.run model (N+1)).1≤64*model.rat (width N H) ∧
      (∀ j≤N,model.rat (binaryWordWidth (j+1))≤address model (PlayerSpecificWidthExecution.run model (N+1)).1) := by
  rw [PlayerSpecificWidthExecution.value]
  have hBW:=PlayerSpecificRationalTrace.control_width (N+1)
  have hwidth : binaryWordWidth (N+1)+8≤width N H := by unfold width; omega
  have hpos:=model.word_le (binaryWordWidth (N+1)+8)
  have haddr : 1≤address model (binaryWordWidth (N+1)) := by unfold address; omega
  refine ⟨haddr,Nat.mul_le_mul_left 64 (model.monotone hwidth),?_⟩
  intro j hj
  have hm:=model.monotone ((binaryWordWidth_mono (Nat.add_le_add_right hj 1)).trans
    (show binaryWordWidth (N+1)≤binaryWordWidth (N+1)+8 by omega))
  unfold address
  omega

theorem measurement_cost (model : RationalCostModel) (N H : ℕ) :
    (PlayerSpecificWidthExecution.run model (N+1)).2≤512*(N+1)*model.rat (width N H) := by
  have hs:=PlayerSpecificWidthExecution.price model (N+1)
  have hBW:=PlayerSpecificRationalTrace.control_width (N+1)
  have hw : PlayerSpecificWidthExecution.width (N+1)≤width N H := by
    unfold PlayerSpecificWidthExecution.width width
    omega
  exact hs.trans (Nat.mul_le_mul (by omega) (model.monotone hw))

theorem callback_cost {N : ℕ} (model : RationalCostModel) (A H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H)
    (hA : A≤64*model.rat (width N H)) (j : Fin N) :
    (callback model A v w j).2≤1000*model.rat (width N H) := by
  have hs:=price_bound model (width N H) (by unfold width; omega) _
    (fits_mono (scalar_fits_height .divide (v.read j) (w.read j) H (hv j) (hw j)) (by unfold width; omega))
  rw [scalar_length] at hs
  have hr : HasHeight [v.read j,w.read j,(scalar .divide (v.read j) (w.read j)).1] (2*H) :=
    cons_height ((hv j).mono (by omega)) (cons_height ((hw j).mono (by omega))
      (cons_height (by simpa only [scalar_value,Arithmetic.apply,two_mul] using (hv j).div (hw j)) (nil_height _)))
  have hc:=price_bound model (width N H) (by unfold width; omega) _ (copyRow_fits _ _
    (fun q hq => (rationalWordWidth_of_height (hr q hq)).trans (by unfold width; omega)) (by simp; unfold width; omega))
  rw [copyRow_length] at hc
  simp only [List.length_cons,List.length_nil] at hc
  simp only [callback]
  nlinarith only [hs,hc,hA]

end Blotto.PlayerSpecificBitRatioSortBudget
