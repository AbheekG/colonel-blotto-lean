import Blotto.ProductAllocationDecoder
import Blotto.RationalEpsilonRejection

/-! A scheduled draw decodes its single selected Cartesian label into a whole
nonnegative rational row. Canonical at-most budget feasibility holds on every
seed. Arbitrary allocation events and marginal CDF events inherit output error. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductBidTree

def scheduledRow (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (bits : Fin (tree.guideTree.scheduledBitBudget E) → Bool) : Fin tree.fields → ℚ :=
  tree.rejectionRow hc budget hm (tree.guideTree.scheduledPrecision E) (tree.guideTree.scheduledAttempts E) fallback bits

theorem scheduledRow_feasible (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget)
    (bits : Fin (tree.guideTree.scheduledBitBudget E) → Bool) :
    Feasible (budget : ℝ) (fun field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) :=
  tree.rejectionRow_feasible hc budget hm _ _ fallback hf bits

noncomputable def targetRow (tree : ProductBidTree) (label : Fin tree.guideTree.real.trueSize) : Allocation tree.fields :=
  tree.realRow (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize))

theorem scheduledRow_eq_targetRow (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (bits : Fin (tree.guideTree.scheduledBitBudget E) → Bool) :
    (fun field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) =
      tree.targetRow ((tree.guideTree.scheduledOutput hc budget hm E (fallback.cast tree.guideTree_trueSize.symm) bits).cast
        tree.guideTree.real_trueSize.symm) := by
  unfold scheduledRow rejectionRow targetRow realRow RationalWeightedGuideTree.scheduledOutput
  congr 1

theorem scheduledRow_event_error (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (event : Set (Allocation tree.fields)) :
    |(fairBitKernel (tree.guideTree.scheduledBitBudget E)).mean
      (fun bits => if (fun field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) ∈ event then 1 else 0) -
      (tree.guideTree.targetKernel budget hm).mean (fun label => if tree.targetRow label ∈ event then 1 else 0)| ≤
        1 / (2 : ℝ) ^ E := by
  have he := tree.guideTree.scheduledOutput_event_error hc budget hm E
    (fallback.cast tree.guideTree_trueSize.symm) {label | tree.targetRow label ∈ event}
  simp_rw [tree.scheduledRow_eq_targetRow hc budget hm E fallback]
  exact he

theorem scheduledRow_cdf_error (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (field : Fin tree.fields) (threshold : ℝ) :
    |(fairBitKernel (tree.guideTree.scheduledBitBudget E)).mean
      (fun bits => if (tree.scheduledRow hc budget hm E fallback bits field : ℝ) ≤ threshold then 1 else 0) -
      (tree.guideTree.targetKernel budget hm).mean (fun label => if tree.targetRow label field ≤ threshold then 1 else 0)| ≤
        1 / (2 : ℝ) ^ E :=
  tree.scheduledRow_event_error hc budget hm E fallback {row | row field ≤ threshold}

end ProductBidTree
end Blotto
