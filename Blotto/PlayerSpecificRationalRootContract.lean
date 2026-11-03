import Blotto.PlayerSpecificRationalRootExecutionCost

/-! Complete original-input rational-root enumeration, linear output sizes
and polynomial source time on one actual cached return. Irreducible-factor
selection and the algebraic field/sampler remain separate obligations. -/
namespace Blotto.PlayerSpecificRationalRootContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 500000

def widthCoefficient : ℕ := 4096*(PlayerSpecificIntegerBudget.coefficient+1)
def workCoefficient : ℕ := 22000000000*(PlayerSpecificIntegerBudget.coefficient+1)
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem source_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootExecution.run model p).2≤workCoefficient*(inputHeight p+1)*
      model.rat (widthCoefficient*(inputHeight p+1)) := by
  have hc:=PlayerSpecificRationalRootExecutionCost.run_cost model p hp hlen
  have hfactor : PlayerSpecificIntegerBudget.height (inputHeight p)+1≤
      (PlayerSpecificIntegerBudget.coefficient+1)*(inputHeight p+1) := by
    unfold PlayerSpecificIntegerBudget.height
    nlinarith
  have hwidth : PlayerSpecificIntegerBudget.width (inputHeight p)≤widthCoefficient*(inputHeight p+1) := by
    have hm:=Nat.mul_le_mul_left 4096 hfactor
    unfold PlayerSpecificIntegerBudget.width widthCoefficient
    nlinarith only [hm]
  have hmul:=Nat.mul_le_mul (Nat.mul_le_mul_left 22000000000 hfactor) (model.monotone hwidth)
  exact hc.trans (hmul.trans_eq (by unfold workCoefficient; ring))

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    let result:=PlayerSpecificRationalRootExecution.run model p
    result.1.length≤3 ∧ (∀ q : ℚ,q∈result.1 ↔ evaluate p q=0) ∧
      HasHeight result.1 (7*inputHeight p+2) ∧
      result.2≤workCoefficient*(inputHeight p+1)*model.rat (widthCoefficient*(inputHeight p+1)) := by
  have hv:=PlayerSpecificRationalRootExecution.value model p
  refine ⟨?_,?_,?_,source_cost model p hp hlen⟩
  · rw [hv]
    exact PlayerSpecificRationalRoots.length_bound p hp hlen
  · rw [hv]
    exact PlayerSpecificRationalRoots.mem_iff p hp hlen
  · intro q hq
    have he:=PlayerSpecificRationalRoots.sound p q (by rw [←hv]; exact hq)
    exact PlayerSpecificRationalRootHeight.root_height p hp hlen q he

theorem polynomial_cost (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootExecution.run RationalCostModel.schoolbook p).2≤polynomialCoefficient*(inputHeight p+1)^3 := by
  have hc:=source_cost RationalCostModel.schoolbook p hp hlen
  change (PlayerSpecificRationalRootExecution.run RationalCostModel.schoolbook p).2≤
    workCoefficient*(inputHeight p+1)*
      ((widthCoefficient*(inputHeight p+1))*(widthCoefficient*(inputHeight p+1))+widthCoefficient*(inputHeight p+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

theorem empty_iff (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootExecution.run model p).1=[] ↔ ∀ q : ℚ,evaluate p q≠0 := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h q hq
    exact h q (((actual_contract model p hp hlen).2.1 q).mpr hq)
  · intro h q hq
    exact h q (((actual_contract model p hp hlen).2.1 q).mp hq)

end Blotto.PlayerSpecificRationalRootContract
