import Blotto.PlayerSpecificRootExecutionCost

/-! Complete original-input fixed-degree root isolation and polynomial bit
time on the same executing return. This closes root isolation, not rational
reconstruction, algebraic field/sign arithmetic or the bounded sampler. -/
namespace Blotto.PlayerSpecificRootContract
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    let result:=PlayerSpecificRootExecution.run model p
    result.1.length≤3 ∧
      (∀ leaf∈result.1,leaf.count=1) ∧
      (∀ leaf∈result.1,∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ leaf.Contains x) ∧
      (∀ x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 → ∃ leaf∈result.1,leaf.Contains x) ∧
      (∀ left∈result.1,∀ right∈result.1,left≠right → ∀ x : ℝ,¬(left.Contains x ∧ right.Contains x)) ∧
      (∀ leaf∈result.1,
        RationalHeight leaf.lo ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1)) ∧
        RationalHeight leaf.hi ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1))) ∧
      result.2≤PlayerSpecificRootExecutionCost.workCoefficient*(inputHeight p+1)*
        model.rat (PlayerSpecificRootExecutionCost.widthCoefficient*(inputHeight p+1)) := by
  have hv:=PlayerSpecificRootExecution.value model p
  refine ⟨?_,?_,?_,?_,?_,?_,PlayerSpecificRootExecutionCost.run_cost model p hp hlen⟩
  · rw [hv]; exact PlayerSpecificRootIsolation.length_le_three p hp hlen
  · rw [hv]; exact PlayerSpecificRootIsolation.counts_one p hp hlen
  · rw [hv]; exact PlayerSpecificRootIsolation.unique_roots p hp hlen
  · intro x hx
    rw [hv]
    exact PlayerSpecificRootIsolation.covers p hp x hx
  · rw [hv]
    intro left hl right hr hne x
    exact PlayerSpecificRootIsolation.disjoint p left right hl hr hne x
  · rw [hv]
    exact fun leaf hl => PlayerSpecificDyadicEndpoints.returned_height_linear p hlen leaf hl

theorem schoolbook_profile (c d s : ℕ) (hs : 1≤s) :
    c*s*((d*s)*(d*s)+d*s)≤c*(d*d+d)*s^3 := by
  have hm:=Nat.mul_le_mul_left (s*s) hs
  have hsq : s^2≤s^3 := by simpa only [pow_succ,pow_two,pow_zero,Nat.one_mul,Nat.mul_one] using hm
  calc
    _ = c*d*d*s^3+c*d*s^2 := by ring
    _ ≤ c*d*d*s^3+c*d*s^3 := Nat.add_le_add_left (Nat.mul_le_mul_left (c*d) hsq) _
    _ = _ := by ring

def polynomialCoefficient : ℕ := PlayerSpecificRootExecutionCost.workCoefficient*
  (PlayerSpecificRootExecutionCost.widthCoefficient*PlayerSpecificRootExecutionCost.widthCoefficient+
    PlayerSpecificRootExecutionCost.widthCoefficient)

theorem polynomial_cost (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRootExecution.run RationalCostModel.schoolbook p).2≤polynomialCoefficient*(inputHeight p+1)^3 := by
  have hc:=PlayerSpecificRootExecutionCost.run_cost RationalCostModel.schoolbook p hp hlen
  change (PlayerSpecificRootExecution.run RationalCostModel.schoolbook p).2≤
    PlayerSpecificRootExecutionCost.workCoefficient*(inputHeight p+1)*
      ((PlayerSpecificRootExecutionCost.widthCoefficient*(inputHeight p+1))*(PlayerSpecificRootExecutionCost.widthCoefficient*(inputHeight p+1))+
        PlayerSpecificRootExecutionCost.widthCoefficient*(inputHeight p+1)) at hc
  exact hc.trans (schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificRootContract
