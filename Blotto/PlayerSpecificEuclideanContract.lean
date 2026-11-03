import Blotto.PlayerSpecificExtendedGCDTraceCost

/-! Actual original-input GCD and Bezout outputs, with mathematical
guarantees, linear coefficient sizes and complete source prices. -/
namespace Blotto.PlayerSpecificEuclideanContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem gcd_contract (model : RationalCostModel) (p q : Data) (hpl : p.length≤4) (hql : q.length≤4) :
    let result := PlayerSpecificGCDExecution.run p q
    let H := PlayerSpecificDivisionContract.inputHeight p q
    Normalized result.1 ∧
    (∀ r : Polynomial ℚ,r∣semantics result.1 ↔ r∣semantics p ∧ r∣semantics q) ∧
    HasHeight result.1 (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧ result.1.length≤4 ∧
    PlayerSpecificRationalTrace.price model result.2≤2000000000*model.rat (PlayerSpecificGCDTraceCost.capWidth H) := by
  have hi := PlayerSpecificDivisionContract.input_heights p q
  let H := PlayerSpecificDivisionContract.inputHeight p q
  have hqH : HasHeight (PlayerSpecificDenseExecution.trim q).1 H := by
    rw [PlayerSpecificDenseExecution.trim_value]
    exact trim_height hi.2.1
  have hql' : (PlayerSpecificDenseExecution.trim q).1.length≤4 := by
    rw [PlayerSpecificDenseExecution.trim_value]
    exact (trim_length q).trans hql
  have hb := PlayerSpecificGCDExecution.loop_bounds (PlayerSpecificDenseExecution.trim q).1.length p
    (PlayerSpecificDenseExecution.trim q).1 H hi.1 hqH hi.2.2 hpl hql' hql'
  exact ⟨PlayerSpecificGCDExecution.normalized p q,PlayerSpecificGCDExecution.common_divisors p q,hb.1,hb.2,
    PlayerSpecificGCDTraceCost.run_cost model p q H hi.1 hi.2.1 hi.2.2 hpl hql⟩

theorem bezout_contract (model : RationalCostModel) (p q : Data) (hpl : p.length≤4) (hql : q.length≤4) :
    let result := PlayerSpecificExtendedGCDExecution.run p q
    let H := PlayerSpecificDivisionContract.inputHeight p q
    semantics result.1.gcd=semantics p*semantics result.1.left+semantics q*semantics result.1.right ∧
    (∀ r : Polynomial ℚ,r∣semantics result.1.gcd ↔ r∣semantics p ∧ r∣semantics q) ∧
    HasHeight result.1.gcd (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
    HasHeight result.1.left (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
    HasHeight result.1.right (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
    result.1.gcd.length≤4 ∧ result.1.left.length≤17 ∧ result.1.right.length≤17 ∧
    PlayerSpecificRationalTrace.price model result.2≤2000000000*model.rat (PlayerSpecificGCDTraceCost.capWidth H) := by
  have hi := PlayerSpecificDivisionContract.input_heights p q
  let H := PlayerSpecificDivisionContract.inputHeight p q
  have hb := PlayerSpecificExtendedGCDExecution.run_bounds p q H hi.1 hi.2.1 hi.2.2 hpl hql
  exact ⟨PlayerSpecificExtendedGCDExecution.identity p q,PlayerSpecificExtendedGCDExecution.common_divisors p q,
    hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2,
    PlayerSpecificExtendedGCDTraceCost.run_cost model p q H hi.1 hi.2.1 hi.2.2 hpl hql⟩

end Blotto.PlayerSpecificEuclideanContract
