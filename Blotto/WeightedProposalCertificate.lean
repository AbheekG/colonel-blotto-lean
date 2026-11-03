import Blotto.WeightedRecursiveProposalLaw
import Blotto.SparseImportanceExecution

/-! The full recursive R160 proposal supplies the sparse importance certificate.
Target weights are exactly the original labelled weights truncated at the
closed budget. Impossible records are retained with their actual zero mass. -/

namespace Blotto
open scoped BigOperators Classical
namespace WeightedGuideTree

noncomputable def feasibleTargetWeight (tree : WeightedGuideTree) (B : ℝ) (x : Fin tree.trueSize) : ℝ :=
  if tree.trueFamily.resource x ≤ B then tree.trueFamily.mass x else 0

noncomputable def recordEquiv (tree : WeightedGuideTree) : tree.ProposalRecord ≃ Fin (Fintype.card tree.ProposalRecord) :=
  Fintype.equivFin _

noncomputable def importanceCertificate (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) :
    SparseImportanceProposal (Fintype.card tree.ProposalRecord) tree.trueSize where
  output := fun p => tree.proposalOutput (tree.recordEquiv.symm p)
  probability := fun p => tree.proposalProbability B (tree.recordEquiv.symm p)
  importance := fun p => tree.proposalImportance B (tree.recordEquiv.symm p)
  targetWeight := tree.feasibleTargetWeight B
  auxiliary := fun p => tree.proposalAuxiliary B (tree.recordEquiv.symm p)
  probability_nonnegative := fun p => tree.proposalProbability_nonnegative B _
  probability_sum := by
    rw [← Equiv.sum_comp tree.recordEquiv]
    simp only [Equiv.symm_apply_apply]
    exact tree.proposalProbability_sum hc B hm
  importance_nonnegative := fun p => tree.proposalImportance_nonnegative B _
  importance_positive := by
    intro p hp
    exact (tree.proposal_positive_contract hc B _ hp).2.2.1
  target_nonnegative := by
    intro x
    unfold feasibleTargetWeight
    split_ifs
    · exact tree.trueFamily.mass_nonnegative x
    · exact le_rfl
  auxiliary_nonnegative := fun p => tree.proposalAuxiliary_nonnegative B _
  auxiliary_fiber_sum := by
    intro x hx
    unfold feasibleTargetWeight at hx
    by_cases hr : tree.trueFamily.resource x ≤ B
    · rw [ite_eq_left hr] at hx
      rw [← Equiv.sum_comp tree.recordEquiv]
      simp only [Equiv.symm_apply_apply]
      exact tree.auxiliaryFiber_normalized hc B x hr hx
    · rw [ite_eq_right hr] at hx
      exact (lt_irrefl 0 hx).elim
  importance_identity := by
    intro p
    rw [tree.proposal_pointwise_identity hc]
    unfold feasibleTargetWeight
    by_cases hr : tree.proposalResource (tree.recordEquiv.symm p) ≤ B
    · change _ = (if tree.proposalResource (tree.recordEquiv.symm p) ≤ B then _ else _) * _
      rw [ite_eq_left hr]
      rfl
    · have ha : tree.proposalAuxiliary B (tree.recordEquiv.symm p) = 0 := by
        have hn := tree.proposalAuxiliary_nonnegative B (tree.recordEquiv.symm p)
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        exact hr (tree.proposalAuxiliary_positive_support B _ hp)
      change _ = (if tree.proposalResource (tree.recordEquiv.symm p) ≤ B then _ else _) * _
      rw [ite_eq_right hr, ha]
      simp

theorem importanceCertificate_targetMass (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) :
    (tree.importanceCertificate hc B hm).targetMass = tree.trueFamily.prefixMass B := rfl

end WeightedGuideTree
end Blotto
