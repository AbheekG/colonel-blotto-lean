import Blotto.IndependentWholeSamplers
import Blotto.WeightedGuideFactorBound

/-! Whole sampled and target laws satisfy canonical support, marginal CDF and
continuous pure-deviation payoff contracts. A target security certificate must
still be produced by the learner; the sampler does not supply Nash selection. -/

namespace Blotto
open scoped Classical
namespace ProductBidTree

theorem epsilonLaw_contract (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget) :
    Supported (budget : ℝ) (tree.epsilonLaw hc budget hm epsilon fallback) ∧
      Supported (budget : ℝ) (tree.targetLaw budget hm) ∧
      CDFClose (tree.epsilonLaw hc budget hm epsilon fallback) (tree.targetLaw budget hm) (epsilon : ℝ) :=
  ⟨tree.epsilonLaw_supported hc budget hm epsilon fallback hf,
    tree.targetLaw_supported budget hm,
    tree.epsilonLaw_CDFClose hc budget hm epsilon he fallback⟩

theorem epsilonLaw_security_close (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) (values : Values tree.fields) (deviationBudget : ℝ) (hB : 0 ≤ deviationBudget) :
    |security values deviationBudget (tree.epsilonLaw hc budget hm epsilon fallback) -
      security values deviationBudget (tree.targetLaw budget hm)| ≤ (epsilon : ℝ) :=
  security_close values hB (tree.epsilonLaw_CDFClose hc budget hm epsilon he fallback)

end ProductBidTree
end Blotto
