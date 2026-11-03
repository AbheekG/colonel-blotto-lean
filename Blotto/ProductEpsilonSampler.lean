import Blotto.ProductScheduledSampler

/-! Arbitrary positive rational accuracy chooses the verified dyadic schedule.
The output is a complete rational allocation row feasible on every seed, with
all allocation-event and ordinary marginal-CDF errors at most epsilon. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductBidTree

def epsilonRow (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.labels) (bits : Fin (tree.guideTree.epsilonBitBudget epsilon) → Bool) : Fin tree.fields → ℚ :=
  tree.scheduledRow hc budget hm (RationalWeightedGuideTree.epsilonPrecision epsilon) fallback bits

theorem epsilonRow_feasible (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget)
    (bits : Fin (tree.guideTree.epsilonBitBudget epsilon) → Bool) :
    Feasible (budget : ℝ) (fun field => (tree.epsilonRow hc budget hm epsilon fallback bits field : ℝ)) :=
  tree.scheduledRow_feasible hc budget hm _ fallback hf bits

theorem epsilonRow_event_error (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) (event : Set (Allocation tree.fields)) :
    |(fairBitKernel (tree.guideTree.epsilonBitBudget epsilon)).mean
      (fun bits => if (fun field => (tree.epsilonRow hc budget hm epsilon fallback bits field : ℝ)) ∈ event then 1 else 0) -
      (tree.guideTree.targetKernel budget hm).mean (fun label => if tree.targetRow label ∈ event then 1 else 0)| ≤ (epsilon : ℝ) :=
  (tree.scheduledRow_event_error hc budget hm _ fallback event).trans
    (RationalWeightedGuideTree.epsilonPrecision_guard epsilon he)

theorem epsilonRow_cdf_error (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) (field : Fin tree.fields) (threshold : ℝ) :
    |(fairBitKernel (tree.guideTree.epsilonBitBudget epsilon)).mean
      (fun bits => if (tree.epsilonRow hc budget hm epsilon fallback bits field : ℝ) ≤ threshold then 1 else 0) -
      (tree.guideTree.targetKernel budget hm).mean (fun label => if tree.targetRow label field ≤ threshold then 1 else 0)| ≤ (epsilon : ℝ) :=
  tree.epsilonRow_event_error hc budget hm epsilon he fallback {row | row field ≤ threshold}

end ProductBidTree
end Blotto
