import Blotto.RationalProposalSeedRefinement
import Blotto.RationalProposalNativeError

/-! The maintained finite-seed sampler now has the exact independent-block
interpretation and a global augmented-Q error. Feasibility is pointwise and
failure is explicit; this closes the proposal law, not guide/runtime/learner costs. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

theorem sampleFinite_mean (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (tree.totalBitBudget K)).mean (fun bits => f (tree.sampleFinite B K bits)) =
      (tree.proposalKernel true B K).mean f := by
  simp_rw [tree.sampleFinite_eq_sampleBlocks]
  exact tree.sampleBlocks_mean B K f

theorem sampleFinite_mean_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (tree.totalBitBudget K)).mean (fun bits => f (tree.sampleFinite B K bits)) -
      ∑ record : tree.Record, (tree.probability B record : ℝ) * f (some record)| ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  simp_rw [tree.sampleFinite_eq_sampleBlocks]
  exact tree.sampleBlocks_mean_error hc B hm K f hf

theorem sampleFinite_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (event : Set (Option tree.Record)) :
    |(fairBitKernel (tree.totalBitBudget K)).mean
      (fun bits => if tree.sampleFinite B K bits ∈ event then 1 else 0) -
      ∑ record : tree.Record, (tree.probability B record : ℝ) * (if some record ∈ event then 1 else 0)| ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  simp_rw [tree.sampleFinite_eq_sampleBlocks]
  exact tree.sampleBlocks_event_error hc B hm K event

theorem sampleFinite_failure_bound (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) :
    (fairBitKernel (tree.totalBitBudget K)).mean
      (fun bits => if tree.sampleFinite B K bits = none then 1 else 0) ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  simp_rw [tree.sampleFinite_eq_sampleBlocks]
  exact tree.sampleBlocks_failure_bound hc B hm K

theorem sampleFinite_error_precision (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) (epsilon : ℝ)
    (hPrecision : (tree.nodes : ℝ) ≤ epsilon * (2 : ℝ) ^ K)
    (event : Set (Option tree.Record)) :
    |(fairBitKernel (tree.totalBitBudget K)).mean
      (fun bits => if tree.sampleFinite B K bits ∈ event then 1 else 0) -
      ∑ record : tree.Record, (tree.probability B record : ℝ) * (if some record ∈ event then 1 else 0)| ≤ epsilon := by
  have he := tree.sampleFinite_event_error hc B hm K event
  have hp : 0 < (2 : ℝ) ^ K := by positivity
  have hBound : (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) ≤ epsilon := by
    rw [mul_one_div]
    exact (div_le_iff₀ hp).mpr hPrecision
  exact he.trans hBound

end RationalWeightedGuideTree
end Blotto
