import Blotto.RationalProposalBlockLaw
import Blotto.RationalProposalIdealKernelLaw
import Blotto.RationalProposalKernelEvents

/-! Actual direct finite-block native proposal has an error against the exact
augmented Q law, on certified positive input. Every event and every bounded
test has nodes*2^-K error; no conditioning on success is hidden. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

theorem sampleBlocks_mean_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (tree.totalBitBudget K)).mean (fun bits => f (tree.sampleBlocks B K bits)) -
      ∑ record : tree.Record, (tree.probability B record : ℝ) * f (some record)| ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  rw [tree.sampleBlocks_mean]
  rw [← tree.proposalKernel_ideal_mean hc B K hm f]
  exact tree.proposalKernel_error B K f hf

theorem sampleBlocks_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (event : Set (Option tree.Record)) :
    |(fairBitKernel (tree.totalBitBudget K)).mean
      (fun bits => if tree.sampleBlocks B K bits ∈ event then 1 else 0) -
      ∑ record : tree.Record, (tree.probability B record : ℝ) * (if some record ∈ event then 1 else 0)| ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  exact tree.sampleBlocks_mean_error hc B hm K (fun x => if x ∈ event then 1 else 0) (by
    intro x
    split_ifs <;> norm_num)

theorem sampleBlocks_failure_bound (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) :
    (fairBitKernel (tree.totalBitBudget K)).mean
      (fun bits => if tree.sampleBlocks B K bits = none then 1 else 0) ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  have he := tree.sampleBlocks_event_error hc B hm K {none}
  simp only [Set.mem_singleton_iff, Option.some_ne_none, ite_false, mul_zero, Finset.sum_const_zero, sub_zero] at he
  exact (le_abs_self _).trans he

end RationalWeightedGuideTree
end Blotto
