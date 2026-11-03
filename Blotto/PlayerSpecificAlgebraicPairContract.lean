import Blotto.PlayerSpecificAlgebraicPairValues

/-! Both executing algebraic branches preserve the pair box and total,
close an endpoint and have the paper's exact expectation-preserving coin.
The bounded random-bit comparison and complete loop remain separate joins. -/
namespace Blotto.PlayerSpecificAlgebraicPairContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicPairStep
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def point (lengthA lengthB a b : Data) (x : ℝ)
    (ha : 0<realEvaluate a x ∧ realEvaluate a x<realEvaluate lengthA x)
    (hb : 0<realEvaluate b x ∧ realEvaluate b x<realEvaluate lengthB x) : RoundingPair :=
  ⟨realEvaluate lengthA x,realEvaluate lengthB x,realEvaluate a x,realEvaluate b x,ha,hb⟩

theorem refinement (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0<realEvaluate a x ∧ realEvaluate a x<realEvaluate lengthA x)
    (hb : 0<realEvaluate b x ∧ realEvaluate b x<realEvaluate lengthB x) :
    let p:=point lengthA lengthB a b x ha hb
    let r:=run model root lengthA lengthB a b
    realEvaluate r.upperA x=p.upper ∧ realEvaluate r.lowerA x=p.lower ∧
      realEvaluate r.upperB x=p.total-p.upper ∧ realEvaluate r.lowerB x=p.total-p.lower ∧
      realEvaluate r.probability x=p.probability := by
  have hu:=PlayerSpecificAlgebraicPairValues.upper model root lengthA lengthB a b hm hirr hv x hx
  have hl:=PlayerSpecificAlgebraicPairValues.lower model root lengthA lengthB a b hm hirr hv x hx
  have huj:=PlayerSpecificAlgebraicPairValues.upper_other model root lengthA lengthB a b x hx.1
  have hlj:=PlayerSpecificAlgebraicPairValues.lower_other model root lengthA lengthB a b x hx.1
  have hp:=PlayerSpecificAlgebraicPairValues.probability model root lengthA lengthB a b hm hirr x hx.1
  rw [hu] at huj
  rw [hl] at hlj
  rw [hu,hl] at hp
  exact ⟨hu,hl,huj,hlj,hp⟩

theorem actual_contract (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0<realEvaluate a x ∧ realEvaluate a x<realEvaluate lengthA x)
    (hb : 0<realEvaluate b x ∧ realEvaluate b x<realEvaluate lengthB x) :
    let r:=run model root lengthA lengthB a b
    (0<realEvaluate r.probability x ∧ realEvaluate r.probability x<1) ∧
      (0≤realEvaluate r.upperA x ∧ realEvaluate r.upperA x≤realEvaluate lengthA x ∧
        0≤realEvaluate r.upperB x ∧ realEvaluate r.upperB x≤realEvaluate lengthB x) ∧
      (0≤realEvaluate r.lowerA x ∧ realEvaluate r.lowerA x≤realEvaluate lengthA x ∧
        0≤realEvaluate r.lowerB x ∧ realEvaluate r.lowerB x≤realEvaluate lengthB x) ∧
      (realEvaluate r.upperA x+realEvaluate r.upperB x=realEvaluate a x+realEvaluate b x) ∧
      (realEvaluate r.lowerA x+realEvaluate r.lowerB x=realEvaluate a x+realEvaluate b x) ∧
      (realEvaluate r.upperA x=0 ∨ realEvaluate r.upperA x=realEvaluate lengthA x ∨
        realEvaluate r.upperB x=0 ∨ realEvaluate r.upperB x=realEvaluate lengthB x) ∧
      (realEvaluate r.lowerA x=0 ∨ realEvaluate r.lowerA x=realEvaluate lengthA x ∨
        realEvaluate r.lowerB x=0 ∨ realEvaluate r.lowerB x=realEvaluate lengthB x) ∧
      (realEvaluate r.probability x*realEvaluate r.upperA x+(1-realEvaluate r.probability x)*realEvaluate r.lowerA x=realEvaluate a x) ∧
      (realEvaluate r.probability x*realEvaluate r.upperB x+(1-realEvaluate r.probability x)*realEvaluate r.lowerB x=realEvaluate b x) := by
  let p:=point lengthA lengthB a b x ha hb
  obtain ⟨hu,hl,huj,hlj,hp⟩:=refinement model root lengthA lengthB a b hm hirr hv x hx ha hb
  dsimp only
  rw [hu,hl,huj,hlj,hp]
  exact ⟨⟨p.probability_pos,p.probability_lt_one⟩,p.branch_feasible (Or.inr rfl),p.branch_feasible (Or.inl rfl),
    p.branch_sum p.upper,p.branch_sum p.lower,p.branch_endpoint (Or.inr rfl),p.branch_endpoint (Or.inl rfl),
    p.expected_resourceI,p.expected_resourceJ⟩

end Blotto.PlayerSpecificAlgebraicPairContract
