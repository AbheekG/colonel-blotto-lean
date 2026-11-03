import Blotto.ConstructedGuideFactor
import Blotto.ProductEpsilonSampler

/-! The actually constructed guide tree has a derived certified factor and
computed bounded rejection schedule. Neither validity nor a small factor is
a separate caller promise; polynomial guide construction/word costs remain open. -/

namespace Blotto
namespace ProductBidTree

theorem constructGuides_local_error (tree : ProductBidTree) :
    tree.constructGuides.guideTree.real.localErrorSum ≤ 1 / 8 := by
  apply WeightedGuideTree.uniform_local_error_budget
  intro gamma hg
  have he := tree.rebuild_factors_same tree.constructionGamma gamma hg
  rw [he]
  change (tree.constructionGamma : ℝ) ≤ 1 + 1 / (8 * (tree.constructGuides.guideTree.real.nodeCount : ℝ))
  unfold constructGuides
  rw [tree.rebuild_factor_count]
  unfold constructionGamma
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
  exact le_rfl

theorem constructGuides_attempts (tree : ProductBidTree) (E : ℕ) :
    tree.constructGuides.guideTree.scheduledAttempts E ≤ 2 * (E + 1) :=
  tree.constructGuides.guideTree.scheduledAttempts_small_error tree.constructGuides_certified tree.constructGuides_local_error E

def constructedBitBudget (tree : ProductBidTree) (epsilon : ℚ) : ℕ :=
  tree.constructGuides.guideTree.epsilonBitBudget epsilon

def constructedEpsilonRow (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.constructGuides.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (epsilon : ℚ) (fallback : Fin tree.constructGuides.labels)
    (bits : Fin (tree.constructedBitBudget epsilon) → Bool) : Fin tree.constructGuides.fields → ℚ :=
  tree.constructGuides.epsilonRow tree.constructGuides_certified budget hm epsilon fallback bits

theorem constructedEpsilonRow_feasible (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.constructGuides.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (epsilon : ℚ) (fallback : Fin tree.constructGuides.labels)
    (hf : tree.constructGuides.resource fallback ≤ budget)
    (bits : Fin (tree.constructedBitBudget epsilon) → Bool) :
    Feasible (budget : ℝ) (fun field => (tree.constructedEpsilonRow budget hm epsilon fallback bits field : ℝ)) :=
  tree.constructGuides.epsilonRow_feasible tree.constructGuides_certified budget hm epsilon fallback hf bits

end ProductBidTree
end Blotto
