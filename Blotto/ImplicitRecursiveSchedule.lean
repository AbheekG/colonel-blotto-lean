import Blotto.ImplicitRecursiveProposal
import Blotto.ImplicitLeafSamplingSchedule

/-! The actual implicit-leaf recursive proposal receives a precision schedule
from node count and requested rational error. Native flat-seed all-test error is
derived; guide-size/full trainer horizon and rejection-target costs are separate. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped Classical

theorem error_node_bound (tree : ProposalTree) (K attempts : ℕ) :
    tree.error K attempts ≤ (tree.projected.nodes : ℝ) *
      (1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts) := by
  induction tree with
  | leaf data guide gamma =>
    simp only [error, projected, RationalWeightedGuideTree.nodes, Nat.cast_one, one_mul, le_refl]
  | fork guide gamma left right ihL ihR =>
    have hExtra : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ attempts := by positivity
    simp only [error, projected, RationalWeightedGuideTree.nodes, Nat.cast_add, Nat.cast_one]
    nlinarith

def nodeTolerance (tree : ProposalTree) (epsilon : ℚ) : ℚ := epsilon / ((tree.projected.nodes : ℚ) + 1)

def precision (tree : ProposalTree) (epsilon : ℚ) : ℕ := leafPrecision (tree.nodeTolerance epsilon)

theorem nodeTolerance_positive (tree : ProposalTree) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < tree.nodeTolerance epsilon := by unfold nodeTolerance; positivity

theorem scheduled_error (tree : ProposalTree) (epsilon : ℚ) (he : 0 < epsilon) :
    tree.error (tree.precision epsilon) (tree.precision epsilon) ≤ (epsilon : ℝ) := by
  have hLocal := leafPrecision_error (tree.nodeTolerance epsilon) (tree.nodeTolerance_positive epsilon he)
  have hNode := tree.error_node_bound (tree.precision epsilon) (tree.precision epsilon)
  have hN : (0 : ℝ) ≤ tree.projected.nodes := by positivity
  have hScale := mul_le_mul_of_nonneg_left hLocal hN
  have hTol : (tree.nodeTolerance epsilon : ℝ) = (epsilon : ℝ) / ((tree.projected.nodes : ℝ) + 1) := by
    simp [nodeTolerance]
  rw [hTol] at hScale
  have heR : (0 : ℝ) ≤ epsilon := by exact_mod_cast he.le
  have hFinal : (tree.projected.nodes : ℝ) * ((epsilon : ℝ) / ((tree.projected.nodes : ℝ) + 1)) ≤ (epsilon : ℝ) := by
    calc
      _ = ((tree.projected.nodes : ℝ) * (epsilon : ℝ)) / ((tree.projected.nodes : ℝ) + 1) := by ring
      _ ≤ (epsilon : ℝ) := (div_le_iff₀ (by positivity : (0 : ℝ) < (tree.projected.nodes : ℝ) + 1)).mpr (by nlinarith)
  exact hNode.trans (hScale.trans hFinal)

theorem scheduled_sample_mean_error (tree : ProposalTree) (budget epsilon : ℚ) (he : 0 < epsilon)
    (test : Option tree.Record → ℝ) (ht : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    |(fairBitKernel (tree.bitBudget (tree.precision epsilon) (tree.precision epsilon))).mean
      (fun bits => test (tree.sample budget (tree.precision epsilon) (tree.precision epsilon) bits)) -
      (tree.kernel false budget (tree.precision epsilon) (tree.precision epsilon)).mean test| ≤ (epsilon : ℝ) :=
  (tree.sample_mean_error budget _ _ test ht).trans (tree.scheduled_error epsilon he)

theorem scheduled_sample_event_error (tree : ProposalTree) (budget epsilon : ℚ) (he : 0 < epsilon)
    (event : Set (Option tree.Record)) :
    |(fairBitKernel (tree.bitBudget (tree.precision epsilon) (tree.precision epsilon))).mean
      (fun bits => if tree.sample budget (tree.precision epsilon) (tree.precision epsilon) bits ∈ event then 1 else 0) -
      (tree.kernel false budget (tree.precision epsilon) (tree.precision epsilon)).mean
        (fun output => if output ∈ event then 1 else 0)| ≤ (epsilon : ℝ) :=
  tree.scheduled_sample_mean_error budget epsilon he (fun output => if output ∈ event then 1 else 0)
    (fun output => by split_ifs <;> norm_num)

end Blotto.ImplicitLeafCounts.ProposalTree
