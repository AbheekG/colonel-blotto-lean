import Blotto.PlayerSpecificCandidateExecutionCost

/-! Unconditional computed root representations for every nonzero cubic:
irreducible defining polynomials, their selected unique real root, complete
original-root coverage, linear stored sizes and polynomial source time. -/
namespace Blotto.PlayerSpecificCandidateContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificCandidateBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem each (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1) :
    Irreducible (semantics candidate.polynomial) ∧ candidate.polynomial.length≤4 ∧
      (∃! x : ℝ,realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) ∧
      (∀ x : ℝ,candidate.interval.Contains x → (realEvaluate candidate.polynomial x=0 ↔ realEvaluate p x=0)) := by
  rw [PlayerSpecificCandidateExecution.value,PlayerSpecificAlgebraicCandidates.run] at hc
  obtain ⟨node,hnode,rfl⟩:=List.mem_map.mp hc
  rw [select_interval]
  exact select_contract p hp hlen node hnode

theorem sizes (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1) :
    HasHeight candidate.polynomial (height p) ∧
      RationalHeight candidate.interval.lo (height p) ∧ RationalHeight candidate.interval.hi (height p) := by
  change candidate∈(PlayerSpecificCandidateRows.run model (PlayerSpecificFactorContract.run model p).1.1
    (PlayerSpecificFactorContract.run model p).1.2 (PlayerSpecificRootExecution.run model p).1).1 at hc
  rw [PlayerSpecificCandidateRows.value] at hc
  obtain ⟨node,hnode,rfl⟩:=List.mem_map.mp hc
  have hf:=factor_bounds model p hp hlen
  have hb:=PlayerSpecificCandidateSelection.bounds model _ _ node (height p) hf.1 hf.2.1 hf.2.2.2 (height_positive p)
  rw [PlayerSpecificCandidateSelection.value] at hb
  rw [select_interval]
  have hn:=node_bounds model p hp hlen node hnode
  exact ⟨hb.1,hn.1,hn.2.1⟩

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    let result:=PlayerSpecificCandidateExecution.run model p
    result.1.length≤3 ∧
      (∀ candidate∈result.1,Irreducible (semantics candidate.polynomial) ∧ candidate.polynomial.length≤4 ∧
        (∃! x : ℝ,realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) ∧
        (∀ x : ℝ,candidate.interval.Contains x → (realEvaluate candidate.polynomial x=0 ↔ realEvaluate p x=0))) ∧
      (∀ x : ℝ,realEvaluate p x=0 → ∃ candidate∈result.1,candidate.interval.Contains x) ∧
      (∀ candidate∈result.1,HasHeight candidate.polynomial (height p) ∧
        RationalHeight candidate.interval.lo (height p) ∧ RationalHeight candidate.interval.hi (height p)) ∧
      result.2≤PlayerSpecificCandidateExecutionCost.workCoefficient*(PlayerSpecificRationalMagnitude.inputHeight p+1)*model.rat (width p) := by
  refine ⟨?_,each model p hp hlen,?_,sizes model p hp hlen,PlayerSpecificCandidateExecutionCost.run_cost model p hp hlen⟩
  · rw [PlayerSpecificCandidateExecution.value]
    exact length_bound p hp hlen
  · rw [PlayerSpecificCandidateExecution.value]
    exact covers p hp

end Blotto.PlayerSpecificCandidateContract
