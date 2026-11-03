import Blotto.RationalWeightedProposalRefinement

/-! Rational proposal auxiliary values and finite record transport exactly
match the real recursive law. Record bijectivity transfers normalization
without enumerating any product table in the native formula evaluator. -/

namespace Blotto
open scoped BigOperators
namespace RationalWeightedGuideTree

theorem auxiliary_real (tree : RationalWeightedGuideTree) (B : ℚ) (record : tree.Record) :
    (tree.auxiliary B record : ℝ) = tree.real.proposalAuxiliary (B : ℝ) (tree.recordReal record) := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    simp only [auxiliary, real, recordReal, WeightedGuideTree.proposalAuxiliary, RationalWeightedFamily.real]
    have he : (family.resource record : ℝ) ≤ (B : ℝ) ↔ family.resource record ≤ B := by norm_cast
    by_cases hq : family.resource record ≤ B
    · rw [ite_eq_left hq, ite_eq_left (he.mpr hq)]
      norm_num
    · rw [ite_eq_right hq, ite_eq_right (mt he.mp hq)]
      norm_num
  | fork guide gamma left right ihL ihR =>
    rcases record with ⟨i, r, l⟩
    simp only [auxiliary, real, WeightedGuideTree.proposalAuxiliary, recordReal,
      WeightedResourceFamily.auxiliaryChoice, Rat.cast_mul, ihL, ihR, Rat.cast_sub,
      guide_resource_real, resource_real]
    have he : left.real.guide.resource (i.cast left.real_guideSize.symm) ≤
        (B : ℝ) - right.real.proposalResource (right.recordReal r) ↔
        left.guide.resource i ≤ B - right.resource r := by
      rw [← guide_resource_real, ← resource_real, ← Rat.cast_sub]
      norm_cast
    by_cases hq : left.guide.resource i ≤ B - right.resource r
    · have hr := he.mpr hq
      rw [ite_eq_left hq, ite_eq_left hr]
      simp only [Rat.cast_div, guide_mass_real, guidePrefix_real, Rat.cast_sub, resource_real]
    · have hr := mt he.mp hq
      rw [ite_eq_right hq, ite_eq_right hr]
      simp

theorem recordReal_bijective (tree : RationalWeightedGuideTree) : Function.Bijective tree.recordReal := by
  induction tree with
  | leaf family guide gamma => exact Function.bijective_id
  | fork guide gamma left right ihL ihR =>
    constructor
    · intro a b hab
      have he : a.1.cast left.real_guideSize.symm = b.1.cast left.real_guideSize.symm ∧
          right.recordReal a.2.1 = right.recordReal b.2.1 ∧
          left.recordReal a.2.2 = left.recordReal b.2.2 := by
        exact ⟨congrArg Prod.fst hab, congrArg (fun x => x.2.1) hab, congrArg (fun x => x.2.2) hab⟩
      have hi : a.1 = b.1 := Fin.ext (congrArg (fun j : Fin left.real.guideSize => j.val) he.1)
      have hr := ihR.1 he.2.1
      have hl := ihL.1 he.2.2
      exact Prod.ext hi (Prod.ext hr hl)
    · intro record
      rcases ihR.2 record.2.1 with ⟨r, hr⟩
      rcases ihL.2 record.2.2 with ⟨l, hl⟩
      refine ⟨(record.1.cast left.real_guideSize, r, l), ?_⟩
      change ((record.1.cast left.real_guideSize).cast left.real_guideSize.symm,
        right.recordReal r, left.recordReal l) = record
      rw [hr, hl]
      have hi : (record.1.cast left.real_guideSize).cast left.real_guideSize.symm = record.1 := Fin.ext rfl
      rw [hi]
      exact Prod.ext rfl (Prod.ext rfl rfl)

noncomputable def recordEquivReal (tree : RationalWeightedGuideTree) : tree.Record ≃ tree.real.ProposalRecord :=
  Equiv.ofBijective tree.recordReal tree.recordReal_bijective

@[reducible] noncomputable def recordFintype (tree : RationalWeightedGuideTree) : Fintype tree.Record :=
  Fintype.ofEquiv tree.real.ProposalRecord tree.recordEquivReal.symm

attribute [instance] recordFintype

theorem probability_sum (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) :
    (∑ record : tree.Record, tree.probability B record) = 1 := by
  have hs := tree.real.proposalProbability_sum hc (B : ℝ) hm
  have he : (∑ record : tree.Record, (tree.probability B record : ℝ)) = 1 := by
    simp_rw [tree.probability_real]
    exact (Equiv.sum_comp tree.recordEquivReal (fun record => tree.real.proposalProbability (B : ℝ) record)).trans hs
  exact_mod_cast he

theorem pointwise_identity (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (record : tree.Record) :
    tree.probability B record * tree.importance B record = tree.weight record * tree.auxiliary B record := by
  have he := tree.real.proposal_pointwise_identity hc (B : ℝ) (tree.recordReal record)
  rw [← probability_real, ← importance_real, ← weight_real, ← auxiliary_real] at he
  exact_mod_cast he

theorem positive_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (record : tree.Record) (hp : 0 < tree.probability B record) : tree.resource record ≤ B := by
  have hpr : 0 < (tree.probability B record : ℝ) := by exact_mod_cast hp
  rw [tree.probability_real] at hpr
  have he := (tree.real.proposal_positive_contract hc (B : ℝ) (tree.recordReal record) hpr).1
  rw [← tree.resource_real] at he
  exact_mod_cast he

end RationalWeightedGuideTree
end Blotto
