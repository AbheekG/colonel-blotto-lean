import Blotto.PlayerSpecificAlgebraicInverseExecution

/-! The actual exact field inverse has reduced output, selected-real value,
linear encoded coefficients and quadratic schoolbook source cost, including
the zero branch and every computed certificate and modular reduction. -/
namespace Blotto.PlayerSpecificAlgebraicInverseContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalMagnitude PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3000000

def inputHeight (m a : Data) : ℕ := PlayerSpecificRationalMagnitude.inputHeight m+PlayerSpecificRationalMagnitude.inputHeight a+1
def heightCoefficient : ℕ := 1000000^17*(2*PlayerSpecificExtendedGCDHeights.linearConstant+1)
def widthCoefficient : ℕ := PlayerSpecificEuclideanBudget.base*65536^5+
  1024*PlayerSpecificExtendedGCDHeights.linearConstant+2048+
  PlayerSpecificModularBudget.base*(heightCoefficient+1)+1024*(heightCoefficient+2)
def polynomialCoefficient : ℕ := 7000000000*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem input_heights (m a : Data) : HasHeight m (inputHeight m a) ∧ HasHeight a (inputHeight m a) ∧ 1 ≤ inputHeight m a := by
  have hm : PlayerSpecificRationalMagnitude.inputHeight m ≤ inputHeight m a := by unfold inputHeight; omega
  have ha : PlayerSpecificRationalMagnitude.inputHeight a ≤ inputHeight m a := by unfold inputHeight; omega
  exact ⟨mono (input_height m) hm,mono (input_height a) ha,by unfold inputHeight; omega⟩

theorem height_profile (P E H : ℕ) : P*(2*(E*(H+1))+1)≤(P*(2*E+1))*(H+1) := by
  have hh : 2*(E*(H+1))+1≤(2*E+1)*(H+1) := by nlinarith
  simpa only [mul_assoc] using Nat.mul_le_mul_left P hh

theorem height_linear (H : ℕ) : PlayerSpecificAlgebraicInverseExecution.height H≤heightCoefficient*(H+1) := by
  unfold PlayerSpecificAlgebraicInverseExecution.height PlayerSpecificModularHeights.height
    PlayerSpecificAlgebraicUnitExecution.outputHeight PlayerSpecificAlgebraicUnitExecution.certificateHeight heightCoefficient
  exact height_profile (1000000^17) PlayerSpecificExtendedGCDHeights.linearConstant H

theorem width_linear (H : ℕ) : PlayerSpecificAlgebraicInverseExecution.width H≤widthCoefficient*(H+1) := by
  have hh:=height_linear H
  have hu : PlayerSpecificAlgebraicUnitExecution.width H≤
      (PlayerSpecificEuclideanBudget.base*65536^5+1024*PlayerSpecificExtendedGCDHeights.linearConstant+2048)*(H+1) := by
    unfold PlayerSpecificAlgebraicUnitExecution.width PlayerSpecificAlgebraicUnitExecution.certificateHeight PlayerSpecificGCDTraceCost.capWidth
    nlinarith
  have hplus : PlayerSpecificAlgebraicInverseExecution.height H+1≤(heightCoefficient+1)*(H+1) := by nlinarith only [hh]
  have hm:=Nat.mul_le_mul_left PlayerSpecificModularBudget.base hplus
  have hmod : PlayerSpecificModularBudget.width 17 (PlayerSpecificAlgebraicUnitExecution.outputHeight H)≤
      PlayerSpecificModularBudget.base*(heightCoefficient+1)*(H+1) := by
    simpa only [PlayerSpecificModularBudget.width,PlayerSpecificAlgebraicInverseExecution.height,mul_assoc] using hm
  have hf : 1024*(PlayerSpecificAlgebraicInverseExecution.height H+H+1)+1024≤1024*(heightCoefficient+2)*(H+1) := by
    nlinarith only [hh]
  have hs:=Nat.add_le_add (Nat.add_le_add hu hmod) hf
  unfold PlayerSpecificAlgebraicInverseExecution.width widthCoefficient
  nlinarith only [hs]

theorem actual_contract (model : RationalCostModel) (m a : Data) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (ha : Reduced m a)
    (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=PlayerSpecificAlgebraicInverseExecution.run model m a
    Reduced m result.1 ∧ result.1.length≤3 ∧ realEvaluate result.1 x=(realEvaluate a x)⁻¹ ∧
      HasHeight result.1 (heightCoefficient*(inputHeight m a+1)) ∧
      result.2≤7000000000*model.rat (widthCoefficient*(inputHeight m a+1)) := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  have hi:=input_heights m a
  have hb:=PlayerSpecificAlgebraicInverseExecution.bounds model m a hm hm0 hml ha (inputHeight m a) hi.1 hi.2.1 hi.2.2
  have hc:=PlayerSpecificAlgebraicInverseExecution.run_cost model m a hm hm0 hml ha (inputHeight m a) hi.1 hi.2.1 hi.2.2
  refine ⟨?_,hb.2,?_,mono hb.1 (height_linear _),hc.trans (Nat.mul_le_mul_left 7000000000 (model.monotone (width_linear _)))⟩
  · rw [PlayerSpecificAlgebraicInverseExecution.value]
    exact PlayerSpecificAlgebraicField.inverse_reduced m a hm hm0
  · rw [PlayerSpecificAlgebraicInverseExecution.value]
    exact PlayerSpecificAlgebraicField.inverse_value m a hm hirr ha x hx

theorem quadratic_profile (c d s : ℕ) (_hs : 1≤s) : c*((d*s)*(d*s)+d*s)≤c*(d*d+d)*s^2 := by
  have hm:=Nat.mul_le_mul_left (c*d) (show s≤s*s by nlinarith)
  nlinarith only [hm]

theorem polynomial_cost (m a : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (hml : m.length≤4) (ha : Reduced m a) (x : ℝ) (hx : realEvaluate m x=0) :
    (PlayerSpecificAlgebraicInverseExecution.run RationalCostModel.schoolbook m a).2≤polynomialCoefficient*(inputHeight m a+1)^2 := by
  have hc:=(actual_contract RationalCostModel.schoolbook m a hm hirr hml ha x hx).2.2.2.2
  change (PlayerSpecificAlgebraicInverseExecution.run RationalCostModel.schoolbook m a).2≤7000000000*
    ((widthCoefficient*(inputHeight m a+1))*(widthCoefficient*(inputHeight m a+1))+widthCoefficient*(inputHeight m a+1)) at hc
  exact hc.trans (quadratic_profile _ _ _ (by omega))

end Blotto.PlayerSpecificAlgebraicInverseContract
