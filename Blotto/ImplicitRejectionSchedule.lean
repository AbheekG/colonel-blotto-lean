import Blotto.ImplicitProposalRejection
import Blotto.ImplicitRecursiveBitBudget
import Blotto.RejectionScheduleBounds

/-! A computed schedule absorbs the implicit uniform-rejection leaf tails and
the acceptance coin error in each whole-record trial. The factor and structural
guide caps remain explicit source obligations; no numeric leaf label loop enters
the seed bound. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree

def rejectionAttempts (tree : ProposalTree) (E : ℕ) : ℕ := rejectionScheduleAttempts tree.projected.factor E
def rejectionPrecision (tree : ProposalTree) (E : ℕ) : ℕ :=
  rejectionSchedulePrecision (2 * tree.projected.nodes) (tree.rejectionAttempts E) E

theorem acceptance_error_node_bound (tree : ProposalTree) (K : ℕ) :
    tree.error K K + 1 / (2 : ℝ) ^ K ≤
      ((2 * tree.projected.nodes : ℕ) + 1 : ℝ) * (1 / (2 : ℝ) ^ K) := by
  have hb := tree.error_node_bound K K
  push_cast
  nlinarith

theorem rejection_schedule_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (E : ℕ) :
    (tree.rejectionAttempts E : ℝ) *
      (tree.error (tree.rejectionPrecision E) (tree.rejectionPrecision E) + 1 / (2 : ℝ) ^ tree.rejectionPrecision E) +
      (1 - 1 / (tree.projected.factor : ℝ)) ^ tree.rejectionAttempts E ≤ 1 / (2 : ℝ) ^ E := by
  have hf : 1 ≤ tree.projected.factor := by
    have he := tree.projected.real.factor_ge_one hc
    rw [← tree.projected.factor_real] at he
    exact_mod_cast he
  have ht := rejectionSchedule_total_error tree.projected.factor hf (2 * tree.projected.nodes) E
  dsimp only at ht
  have hb := mul_le_mul_of_nonneg_left (tree.acceptance_error_node_bound (tree.rejectionPrecision E))
    (Nat.cast_nonneg (tree.rejectionAttempts E) : (0 : ℝ) ≤ tree.rejectionAttempts E)
  exact (add_le_add_left hb _).trans ht

theorem rejectionPrecision_word_bound (tree : ProposalTree) (E : ℕ) :
    tree.rejectionPrecision E ≤ E + 1 + binaryWordWidth (tree.rejectionAttempts E) +
      binaryWordWidth (2 * tree.projected.nodes + 1) :=
  rejectionSchedulePrecision_bound _ _ _

theorem rejectionAttempts_factor_bound (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (E : ℕ) :
    (tree.rejectionAttempts E : ℚ) ≤ (tree.projected.factor + 1) * (E + 1) := by
  have hf : 0 ≤ tree.projected.factor := by
    have he := tree.projected.real.factor_ge_one hc
    rw [← tree.projected.factor_real] at he
    exact_mod_cast (show (0 : ℝ) ≤ (tree.projected.factor : ℝ) by linarith)
  exact rejectionScheduleAttempts_bound _ hf E

def rejectionSeedBudget (tree : ProposalTree) (E : ℕ) : ℕ :=
  tree.rejectionAttempts E * tree.attemptBitBudget (tree.rejectionPrecision E) (tree.rejectionPrecision E)

theorem rejectionSeedBudget_bound (tree : ProposalTree) (blocks width guideSize E : ℕ)
    (h : tree.StructuralCaps blocks width guideSize) :
    tree.rejectionSeedBudget E ≤ tree.rejectionAttempts E *
      (3 * (tree.leaves * blocks + tree.forks * guideSize) +
        tree.rejectionPrecision E * (3 * tree.projected.nodes + tree.leaves * width + 3) + 3) := by
  have hb := tree.bitBudget_structural_bound blocks width guideSize (tree.rejectionPrecision E) (tree.rejectionPrecision E) h
  unfold rejectionSeedBudget attemptBitBudget
  apply Nat.mul_le_mul_left
  nlinarith

end Blotto.ImplicitLeafCounts.ProposalTree
