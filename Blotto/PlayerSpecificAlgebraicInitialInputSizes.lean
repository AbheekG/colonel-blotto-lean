import Blotto.PlayerSpecificAlgebraicInitialHeights

/-! Actual cached inverse and every initial field coefficient have
polynomial ORIGINAL-input height. Only a fixed three-layer algebraic
envelope is iterated; there is no iteration over the number of fields. -/
namespace Blotto.PlayerSpecificAlgebraicInitialInputSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicInitialVector PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def base (N L : ℕ) : ℕ := PlayerSpecificFiniteParameterSizes.height N L+L+2
def height (N L : ℕ) : ℕ := PlayerSpecificAlgebraicInitialHeights.height (base N L)

theorem actual_sizes {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    HasHeight (prepare RationalCostModel.schoolbook i r).inverseScale (step (base N (inputSize i))) ∧
      ∀ j,HasHeight ((prepare RationalCostModel.schoolbook i r).rows.read j).length (height N (inputSize i)) ∧
        HasHeight ((prepare RationalCostModel.schoolbook i r).rows.read j).initialA (height N (inputSize i)) ∧
        HasHeight ((prepare RationalCostModel.schoolbook i r).rows.read j).initialB (height N (inputSize i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hsize:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hbase : PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤base N (inputSize i) := by unfold base; omega
  have hL : inputSize i≤base N (inputSize i) := by unfold base; omega
  have hpositive : 1≤base N (inputSize i) := by unfold base; omega
  have hmH:=PlayerSpecificPolynomialHeights.mono hsize.1 hbase
  have hscaleH:=PlayerSpecificPolynomialHeights.mono hsize.2.2.2.1 hbase
  have hi:=inverse_height r.root.polynomial r.scale (base N (inputSize i)) hs.1 hm0 hs.2.2.1 hs.2.2.2.1 hmH hscaleH hpositive
  have hiR:=PlayerSpecificAlgebraicField.inverse_reduced r.root.polynomial r.scale hs.1 hm0
  refine ⟨hi,?_⟩
  intro j
  rw [read]
  exact PlayerSpecificAlgebraicInitialHeights.result_heights RationalCostModel.schoolbook r.root _ _ _ (base N (inputSize i))
    hs.1 hm0 hs.2.2.1 hmH ((PlayerSpecificRecognitionInputHeights.original_fields i).2.1 j |>.mono hL)
    ((PlayerSpecificRecognitionInputHeights.original_fields i).2.2 j |>.mono hL) hpositive hiR hi

theorem polynomial_profile (C K N L F h : ℕ) (hF : F≤11*C*(N+1)*(L+1)) (hh : h≤K*(F+L+2+1)) :
    h≤(K*(11*C+4))*(N+1)*(L+1) := by
  have hs : 1≤(N+1)*(L+1) := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)
  have hl : L+1≤(N+1)*(L+1) := by nlinarith
  have hbase : F+L+2+1≤(11*C+4)*((N+1)*(L+1)) := by nlinarith only [hF,hs,hl]
  have hm:=Nat.mul_le_mul_left K hbase
  nlinarith only [hh,hm]

theorem polynomial_height (N L : ℕ) : height N L≤
    (((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3)*(11*PlayerSpecificFiniteScaleHeights.coefficient+4))*(N+1)*(L+1) :=
  polynomial_profile PlayerSpecificFiniteScaleHeights.coefficient ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) N L _ _
    (PlayerSpecificFiniteParameterSizes.polynomial_height N L)
    (PlayerSpecificAlgebraicInitialHeights.linear_height (base N L))

end Blotto.PlayerSpecificAlgebraicInitialInputSizes
