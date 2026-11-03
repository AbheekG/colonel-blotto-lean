import Blotto.PlayerSpecificFactorExecutionCost

/-! Complete original-input factor removal: multiplicities, decomposition,
irreducibility of a nonconstant residual, linear encoding and polynomial
source cost all concern the same executing return. -/
namespace Blotto.PlayerSpecificFactorContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 3000000

def growthCoefficient : ℕ := 4000000^4+1
def widthCoefficient : ℕ := PlayerSpecificFactorBudget.widthCoefficient*growthCoefficient
def workCoefficient : ℕ := 5*PlayerSpecificFactorBudget.workCoefficient*growthCoefficient
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)
def run (model : RationalCostModel) (p : Data) : (Data×Data)×ℕ := PlayerSpecificFactorExecution.run model p.length p

theorem value (model : RationalCostModel) (p : Data) : (run model p).1=PlayerSpecificRationalFactors.factor p :=
  PlayerSpecificFactorExecution.value model p.length p

theorem growth (p : Data) (hlen : p.length≤4) :
    PlayerSpecificFactorHeights.height p.length (inputHeight p)+1≤growthCoefficient*(inputHeight p+1) := by
  have hh:=PlayerSpecificFactorHeights.linear_bound p.length (inputHeight p)
  have hp:=Nat.pow_le_pow_right (by decide : 1≤(4000000:ℕ)) hlen
  have hm:=Nat.mul_le_mul_right (inputHeight p+1) hp
  unfold growthCoefficient
  nlinarith only [hh,hm]

theorem source_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (run model p).2≤workCoefficient*(inputHeight p+1)*model.rat (widthCoefficient*(inputHeight p+1)) := by
  have hc:=PlayerSpecificFactorExecutionCost.run_cost model p.length p hp hlen (le_refl _) hlen
    (inputHeight p) (input_height p) (by unfold inputHeight; omega)
  have hg:=growth p hlen
  have hw : PlayerSpecificFactorBudget.width (PlayerSpecificFactorHeights.height p.length (inputHeight p))≤
      widthCoefficient*(inputHeight p+1) := by
    have hm:=Nat.mul_le_mul_left PlayerSpecificFactorBudget.widthCoefficient hg
    simpa only [PlayerSpecificFactorBudget.width,widthCoefficient,mul_assoc] using hm
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right PlayerSpecificFactorBudget.workCoefficient
    (show p.length+1≤5 by omega)) hg) (model.monotone hw)
  exact hc.trans (hm.trans_eq (by unfold workCoefficient; ring))

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    let result:=run model p
    PlayerSpecificPolynomialNormalization.Normalized result.1.2 ∧ semantics result.1.2≠0 ∧
      (∀ q : ℚ,evaluate result.1.2 q≠0) ∧
      semantics p=PlayerSpecificRationalFactors.product result.1.1*semantics result.1.2 ∧
      result.1.1.length≤3 ∧ result.1.2.length≤4 ∧
      (∀ q ∈ result.1.1,evaluate p q=0) ∧
      HasHeight result.1.1 (growthCoefficient*(inputHeight p+1)) ∧
      HasHeight result.1.2 (growthCoefficient*(inputHeight p+1)) ∧
      (0<(semantics result.1.2).natDegree → Irreducible (semantics result.1.2)) ∧
      result.2≤workCoefficient*(inputHeight p+1)*model.rat (widthCoefficient*(inputHeight p+1)) := by
  have hc:=PlayerSpecificRationalFactors.factor_contract p hp hlen
  have hb:=PlayerSpecificFactorExecutionCost.output_bounds model p.length p hp hlen (le_refl _)
    (inputHeight p) (input_height p)
  have hg: PlayerSpecificFactorHeights.height p.length (inputHeight p)≤growthCoefficient*(inputHeight p+1) :=
    (Nat.le_succ _).trans (growth p hlen)
  refine ⟨?_,?_,?_,?_,hb.2.2.1,hb.2.2.2,?_,mono hb.1 hg,mono hb.2.1 hg,?_,source_cost model p hp hlen⟩
  · rw [value]; exact hc.1
  · rw [value]; exact hc.2.1
  · rw [value]; exact hc.2.2.1
  · rw [value]; exact hc.2.2.2.1
  · rw [value]; exact hc.2.2.2.2.2.2
  · rw [value]; exact PlayerSpecificRationalFactors.residual_irreducible p hp hlen

theorem polynomial_cost (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (run RationalCostModel.schoolbook p).2≤polynomialCoefficient*(inputHeight p+1)^3 := by
  have hc:=source_cost RationalCostModel.schoolbook p hp hlen
  change (run RationalCostModel.schoolbook p).2≤workCoefficient*(inputHeight p+1)*
    ((widthCoefficient*(inputHeight p+1))*(widthCoefficient*(inputHeight p+1))+widthCoefficient*(inputHeight p+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificFactorContract
