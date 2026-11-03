import Blotto.PlayerSpecificAlgebraicInverseContract

/-! Original-input modular multiplication/certificate reduction with exact
selected-root value, reduced linear-size output and quadratic source time. -/
namespace Blotto.PlayerSpecificModularContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3000000

def inputHeight (m b a : Data) : ℕ := PlayerSpecificRationalMagnitude.inputHeight m+
  PlayerSpecificRationalMagnitude.inputHeight b+PlayerSpecificRationalMagnitude.inputHeight a+1
def heightCoefficient : ℕ := 1000000^17
def widthCoefficient : ℕ := PlayerSpecificModularBudget.base*(heightCoefficient+1)
def polynomialCoefficient : ℕ := 3600000000*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem input_heights (m b a : Data) :
    HasHeight m (inputHeight m b a) ∧ HasHeight b (inputHeight m b a) ∧ HasHeight a (inputHeight m b a) := by
  have hm : PlayerSpecificRationalMagnitude.inputHeight m ≤ inputHeight m b a := by unfold inputHeight; omega
  have hb : PlayerSpecificRationalMagnitude.inputHeight b ≤ inputHeight m b a := by unfold inputHeight; omega
  have ha : PlayerSpecificRationalMagnitude.inputHeight a ≤ inputHeight m b a := by unfold inputHeight; omega
  exact ⟨mono (input_height m) hm,mono (input_height b) hb,mono (input_height a) ha⟩

theorem linear_bounds (a : Data) (hlen : a.length≤17) (H : ℕ) :
    PlayerSpecificModularHeights.height a.length H≤heightCoefficient*(H+1) ∧
      PlayerSpecificModularBudget.width a.length H≤widthCoefficient*(H+1) := by
  have hh : PlayerSpecificModularHeights.height a.length H≤heightCoefficient*(H+1) :=
    PlayerSpecificModularHeights.fuel_mono H hlen
  have hp : PlayerSpecificModularHeights.height a.length H+1≤(heightCoefficient+1)*(H+1) := by nlinarith only [hh]
  have hm:=Nat.mul_le_mul_left PlayerSpecificModularBudget.base hp
  exact ⟨hh,by simpa only [PlayerSpecificModularBudget.width,widthCoefficient,mul_assoc] using hm⟩

theorem actual_contract (model : RationalCostModel) (m b a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hbl : b.length≤3) (hal : a.length≤17) (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=PlayerSpecificModularExecution.run model m b a
    Reduced m result.1 ∧ result.1.length≤3 ∧ realEvaluate result.1 x=realEvaluate a x*realEvaluate b x ∧
      HasHeight result.1 (heightCoefficient*(inputHeight m b a+1)) ∧
      result.2≤3600000000*model.rat (widthCoefficient*(inputHeight m b a+1)) := by
  have hi:=input_heights m b a
  have hh:=PlayerSpecificModularHeights.run_height m b a hm hm0 hml hbl (inputHeight m b a) hi.1 hi.2.1 hi.2.2
  have hb:=linear_bounds a hal (inputHeight m b a)
  have hc:=PlayerSpecificModularExecutionCost.run_cost model m b a hm hm0 hml hbl hal (inputHeight m b a) hi.1 hi.2.1 hi.2.2
  have hwork : 200000000*(a.length+1)≤3600000000 := by omega
  have hprice:=hc.trans (Nat.mul_le_mul hwork (model.monotone hb.2))
  have hred:=PlayerSpecificModularHorner.reduced m b a hm hm0
  dsimp only
  simp only [PlayerSpecificModularExecution.value]
  exact ⟨hred,by have hl:=hred.2; omega,PlayerSpecificModularHorner.real_value m b a x hx,mono hh hb.1,hprice⟩

theorem polynomial_cost (m b a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hbl : b.length≤3) (hal : a.length≤17) (x : ℝ) (hx : realEvaluate m x=0) :
    (PlayerSpecificModularExecution.run RationalCostModel.schoolbook m b a).2≤polynomialCoefficient*(inputHeight m b a+1)^2 := by
  have hc:=(actual_contract RationalCostModel.schoolbook m b a hm hm0 hml hbl hal x hx).2.2.2.2
  change (PlayerSpecificModularExecution.run RationalCostModel.schoolbook m b a).2≤3600000000*
    ((widthCoefficient*(inputHeight m b a+1))*(widthCoefficient*(inputHeight m b a+1))+widthCoefficient*(inputHeight m b a+1)) at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile _ _ _ (by omega))

end Blotto.PlayerSpecificModularContract
