import Blotto.PlayerSpecificDivisionTraceCost

/-! Actual original-input rational polynomial division with correctness,
normalization, size and source-price guarantees on the same return. -/
namespace Blotto.PlayerSpecificDivisionContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 4000000

def inputHeight (p q : Data) : ℕ := PlayerSpecificRationalMagnitude.inputHeight p+PlayerSpecificRationalMagnitude.inputHeight q+1

theorem input_heights (p q : Data) : HasHeight p (inputHeight p q) ∧ HasHeight q (inputHeight p q) ∧ 1 ≤ inputHeight p q := by
  have hp := input_height p
  have hq := input_height q
  exact ⟨mono (t := inputHeight p q) hp (by unfold inputHeight; omega),
    mono (t := inputHeight p q) hq (by unfold inputHeight; omega),by unfold inputHeight; omega⟩

theorem actual_contract (model : RationalCostModel) (p q : Data) (hpl : p.length≤4) (hql : q.length≤4) :
    let result := PlayerSpecificDivisionExecution.run p q
    Normalized result.1.1 ∧ Normalized result.1.2 ∧
    semantics q*semantics result.1.1+semantics result.1.2=semantics p ∧
    (semantics q≠0 → (semantics result.1.2).degree<(semantics q).degree) ∧
    HasHeight result.1.1 (32211*inputHeight p q+9666) ∧
    HasHeight result.1.2 (32211*inputHeight p q+9666) ∧
    result.1.1.length≤p.length ∧ result.1.2.length≤p.length ∧
    PlayerSpecificRationalTrace.price model result.2≤
      100000000*model.rat (2*1000000^6*(inputHeight p q+1)) := by
  have hi := input_heights p q
  have hn := PlayerSpecificDivisionExecution.normalized p q
  have hh := PlayerSpecificDivisionExecution.heights p q (inputHeight p q) hi.1 hi.2.1 hi.2.2 hpl hql
  have hl := PlayerSpecificDivisionExecution.lengths p q
  have hc := PlayerSpecificDivisionTraceCost.run_cost model p q (inputHeight p q) hi.1 hi.2.1 hi.2.2 hpl hql
  refine ⟨hn.1,hn.2,?_,?_,hh.1,hh.2,hl.1,hl.2,hc⟩
  · rw [PlayerSpecificDivisionExecution.value]
    exact PlayerSpecificPolynomialDivision.reconstruction p q
  · intro hq
    rw [PlayerSpecificDivisionExecution.value]
    exact PlayerSpecificPolynomialDivision.remainder_degree p q hq

end Blotto.PlayerSpecificDivisionContract
