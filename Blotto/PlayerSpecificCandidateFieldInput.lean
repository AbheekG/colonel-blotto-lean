import Blotto.PlayerSpecificAlgebraicField

/-! The actual candidate preparation supplies the normalized irreducible
defining polynomial required by the exact reduced field backend. -/
namespace Blotto.PlayerSpecificCandidateFieldInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem normalized (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1) :
    Normalized candidate.polynomial := by
  rw [PlayerSpecificCandidateExecution.value,PlayerSpecificAlgebraicCandidates.run] at hc
  obtain ⟨node,hnode,rfl⟩:=List.mem_map.mp hc
  cases he : lookup (PlayerSpecificRationalFactors.factor p).1 node with
  | none =>
    simp only [select,he]
    exact (PlayerSpecificRationalFactors.factor_contract p hp hlen).1
  | some q =>
    simp only [select,he]
    apply Or.inr
    simp only [PlayerSpecificLinearFactor.linear,List.getLast?_cons_cons,List.getLast?_singleton,Option.getD_some]
    norm_num

theorem field_input (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1) :
    Normalized candidate.polynomial ∧ Irreducible (semantics candidate.polynomial) ∧
      candidate.polynomial.length≤4 ∧ 2≤candidate.polynomial.length ∧
      (∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) := by
  have hn:=normalized model p hp hlen candidate hc
  have hs:=PlayerSpecificCandidateContract.each model p hp hlen candidate hc
  obtain ⟨x,hx,_⟩:=hs.2.2.1
  have hd:=PlayerSpecificFactorRealRoots.positive_degree candidate.polynomial hs.1.ne_zero x hx.1
  have hl:=degree_le candidate.polynomial
  exact ⟨hn,hs.1,hs.2.1,by omega,hs.2.2.1⟩

end Blotto.PlayerSpecificCandidateFieldInput
