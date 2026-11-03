import Blotto.WeightedProposalCertificate

/-! Recursive proposal importance has a uniform bound even on impossible
records. A certified lower guide therefore supplies an exact finite rejection
attempt with the correct budget-truncated target weights. -/

namespace Blotto
open scoped BigOperators Classical
namespace WeightedGuideTree

theorem proposalImportance_bound (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (record : tree.ProposalRecord) :
    tree.proposalImportance B record ≤ tree.factor * tree.guide.prefixMass B := by
  induction tree generalizing B with
  | leaf family guide gamma => exact (hc.2 B).2
  | fork guide gamma left right ihLeft ihRight =>
    let HL := left.guide.prefixMass (B - right.proposalResource record.2.1)
    let HR := right.guide.prefixMass (B - left.guide.resource record.1)
    have hL := ihLeft hc.2.1 (B - right.proposalResource record.2.1) record.2.2
    have hR := ihRight hc.2.2.1 (B - left.guide.resource record.1) record.2.1
    have hZ0 := left.guide.convolution_nonnegative right.guide B
    by_cases hl : 0 < HL
    · by_cases hr : 0 < HR
      · have hRL : left.proposalImportance (B - right.proposalResource record.2.1) record.2.2 / HL ≤ left.factor := by
          apply (div_le_iff₀ hl).mpr
          simpa only [HL, mul_comm] using hL
        have hRR : right.proposalImportance (B - left.guide.resource record.1) record.2.1 / HR ≤ right.factor := by
          apply (div_le_iff₀ hr).mpr
          simpa only [HR, mul_comm] using hR
        have hBound := WeightedProposalStep.importance_bound hZ0
          (right.proposalImportance_nonnegative _ _) hl hr (left.factor_nonnegative hc.2.1) hRL hRR
        have hLocal := (hc.2.2.2 B).2
        change WeightedProposalStep.importance _ _ _ HL HR ≤ _
        calc
          _ ≤ left.guide.convolution right.guide B * left.factor * right.factor := hBound
          _ ≤ (gamma * guide.prefixMass B) * left.factor * right.factor :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLocal (left.factor_nonnegative hc.2.1))
              (right.factor_nonnegative hc.2.2.1)
          _ = _ := by change _ = (left.factor * right.factor * gamma) * guide.prefixMass B; ring
      · have hz : HR = 0 := le_antisymm (le_of_not_gt hr) (right.guide.prefix_nonnegative _)
        change WeightedProposalStep.importance _ _ _ HL HR ≤ _
        simp only [WeightedProposalStep.importance, hz, mul_zero, div_zero]
        exact mul_nonneg ((fork guide gamma left right).factor_nonnegative hc) (guide.prefix_nonnegative B)
    · have hz : HL = 0 := le_antisymm (le_of_not_gt hl) (left.guide.prefix_nonnegative _)
      change WeightedProposalStep.importance _ _ _ HL HR ≤ _
      simp only [WeightedProposalStep.importance, hz, zero_mul, div_zero]
      exact mul_nonneg ((fork guide gamma left right).factor_nonnegative hc) (guide.prefix_nonnegative B)

theorem importanceCertificate_bound (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) (p : Fin (Fintype.card tree.ProposalRecord)) :
    (tree.importanceCertificate hc B hm).importance p ≤ tree.factor * tree.guide.prefixMass B :=
  tree.proposalImportance_bound hc B _

theorem importanceCertificate_coin_bound (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) (p : Fin (Fintype.card tree.ProposalRecord)) :
    (tree.importanceCertificate hc B hm).importance p ≤ tree.guide.prefixMass B * tree.factor := by
  simpa only [mul_comm] using tree.importanceCertificate_bound hc B hm p

theorem importanceCertificate_acceptance (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) :
    let cert := tree.importanceCertificate hc B hm
    let bound := tree.guide.prefixMass B * tree.factor
    0 < bound ∧ cert.acceptanceMass bound ≤ 1 ∧ 1 / tree.factor ≤ cert.acceptanceMass bound := by
  dsimp only
  have hg := (tree.prefix_positive_iff hc B).mpr hm
  have hf : 0 < tree.factor := by linarith [tree.factor_ge_one hc]
  have hb := mul_pos hg hf
  refine ⟨hb, ?_, ?_⟩
  · apply SparseImportanceProposal.acceptanceMass_le_one _ hb
    intro p
    simpa only [mul_comm] using tree.importanceCertificate_bound hc B hm p
  · apply SparseImportanceProposal.acceptance_lower_bound _ hg hf
    rw [tree.importanceCertificate_targetMass]
    exact (tree.lower_envelope hc B).1

theorem rejection_output_target (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (hm : 0 < tree.trueFamily.prefixMass B) (k : ℕ) (x : Fin tree.trueSize) :
    let cert := tree.importanceCertificate hc B hm
    let bound := tree.guide.prefixMass B * tree.factor
    let hb := (tree.importanceCertificate_acceptance hc B hm).1
    let hBound := tree.importanceCertificate_coin_bound hc B hm
    (cert.attempt bound hb hBound).pathMean k
      (fun path => if (cert.attempt bound hb hBound).run k path = some x then 1 else 0) =
        (1 - rejectionFailure (cert.acceptanceMass bound) k) *
          (tree.feasibleTargetWeight B x / tree.trueFamily.prefixMass B) := by
  dsimp only
  rw [SparseImportanceProposal.run_output_target _ _ _ (by rw [tree.importanceCertificate_targetMass]; exact hm),
    tree.importanceCertificate_targetMass]
  rfl

end WeightedGuideTree
end Blotto
