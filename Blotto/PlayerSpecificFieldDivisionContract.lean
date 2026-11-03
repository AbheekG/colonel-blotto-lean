import Blotto.PlayerSpecificFieldDivisionCost

/-! Exact division, linear original-input coefficient sizes and complete
quadratic schoolbook source time are joined on the actual cached caller. -/
namespace Blotto.PlayerSpecificFieldDivisionContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3000000

def heightCoefficient : ℕ := 1000000^3*(PlayerSpecificAlgebraicInverseContract.heightCoefficient+2)
def widthCoefficient : ℕ := PlayerSpecificAlgebraicInverseContract.widthCoefficient+
  PlayerSpecificModularBudget.base*(heightCoefficient+1)+1024*(heightCoefficient+2)
def polynomialCoefficient : ℕ := 8000000000*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem growth_profile (P A H v : ℕ) (hv : v≤A*(H+1)) : P*(v+H+1+1)≤(P*(A+2))*(H+1) := by
  have hs : v+H+1+1≤(A+2)*(H+1) := by nlinarith only [hv]
  simpa only [mul_assoc] using Nat.mul_le_mul_left P hs

theorem height_linear (H : ℕ) : PlayerSpecificFieldDivisionExecution.height H≤heightCoefficient*(H+1) := by
  unfold PlayerSpecificFieldDivisionExecution.height PlayerSpecificModularHeights.height
    PlayerSpecificFieldDivisionExecution.coefficientHeight heightCoefficient
  exact growth_profile (1000000^3) PlayerSpecificAlgebraicInverseContract.heightCoefficient H
    (PlayerSpecificAlgebraicInverseExecution.height H) (PlayerSpecificAlgebraicInverseContract.height_linear H)

theorem width_linear (H : ℕ) : PlayerSpecificFieldDivisionExecution.width H≤widthCoefficient*(H+1) := by
  have hi:=PlayerSpecificAlgebraicInverseContract.width_linear H
  have hh:=height_linear H
  have hs : PlayerSpecificFieldDivisionExecution.height H+1≤(heightCoefficient+1)*(H+1) := by nlinarith only [hh]
  have hm:=Nat.mul_le_mul_left PlayerSpecificModularBudget.base hs
  have hmod : PlayerSpecificModularBudget.width 3 (PlayerSpecificFieldDivisionExecution.coefficientHeight H)≤
      PlayerSpecificModularBudget.base*(heightCoefficient+1)*(H+1) := by
    simpa only [PlayerSpecificModularBudget.width,PlayerSpecificFieldDivisionExecution.height,mul_assoc] using hm
  have hf : 1024*(PlayerSpecificFieldDivisionExecution.height H+H+1)+1024≤1024*(heightCoefficient+2)*(H+1) := by
    nlinarith only [hh]
  have hsum:=Nat.add_le_add (Nat.add_le_add hi hmod) hf
  unfold PlayerSpecificFieldDivisionExecution.width widthCoefficient
  nlinarith only [hsum]

theorem actual_contract (model : RationalCostModel) (m a b : Data) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b)
    (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=PlayerSpecificFieldDivisionExecution.run model m a b
    Reduced m result.1 ∧ result.1.length≤3 ∧ realEvaluate result.1 x=realEvaluate a x/realEvaluate b x ∧
      HasHeight result.1 (heightCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)) ∧
      result.2≤8000000000*model.rat (widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)) := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  have hi:=PlayerSpecificFieldCombinationContract.input_heights m a b
  have hout:=PlayerSpecificFieldDivisionExecution.bounds model m a b hm hm0 hml ha hb _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hc:=PlayerSpecificFieldDivisionCost.run_cost model m a b hm hm0 hml ha hb _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  refine ⟨hout.1,hout.2.1,?_,mono hout.2.2 (height_linear _),hc.trans (Nat.mul_le_mul_left 8000000000 (model.monotone (width_linear _)))⟩
  rw [PlayerSpecificFieldDivisionExecution.value]
  exact PlayerSpecificAlgebraicField.divide_value m a b hm hirr hb x hx

theorem polynomial_cost (m a b : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b) (x : ℝ) (hx : realEvaluate m x=0) :
    (PlayerSpecificFieldDivisionExecution.run RationalCostModel.schoolbook m a b).2≤
      polynomialCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)^2 := by
  have hc:=(actual_contract RationalCostModel.schoolbook m a b hm hirr hml ha hb x hx).2.2.2.2
  change (PlayerSpecificFieldDivisionExecution.run RationalCostModel.schoolbook m a b).2≤8000000000*
    ((widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1))*
      (widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1))+
        widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)) at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile _ _ _ (by omega))

end Blotto.PlayerSpecificFieldDivisionContract
