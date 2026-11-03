import Blotto.ProductSamplerLawEvents
import Blotto.ProductTargetSupport

/-! The actual whole-row probability laws now inherit continuous-deviation
payoff/regret stability, including highest half ties and zero bids. A learner
still must supply the target security/Nash certificate; none is assumed closed. -/

namespace Blotto
open MeasureTheory Set
open scoped Classical
namespace ProductBidTree

theorem epsilonLaw_CDFClose (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) :
    CDFClose (tree.epsilonLaw hc budget hm epsilon fallback) (tree.targetLaw budget hm) (epsilon : ℝ) := by
  intro field threshold
  have h := tree.scheduledLaw_CDFClose hc budget hm (RationalWeightedGuideTree.epsilonPrecision epsilon) fallback field threshold
  exact h.trans (RationalWeightedGuideTree.epsilonPrecision_guard epsilon he)

theorem epsilonLaw_purePayoff_close (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.labels) (values : Values tree.fields) (row : Allocation tree.fields) :
    |purePayoff values row (tree.epsilonLaw hc budget hm epsilon fallback) - purePayoff values row (tree.targetLaw budget hm)| ≤ (epsilon : ℝ) :=
  purePayoff_close values (tree.epsilonLaw_CDFClose hc budget hm epsilon he fallback) row

end ProductBidTree

-- Field-count equality is kept explicit for two independently prepared players.
theorem productSampler_regret_stability {n : ℕ} (valuesA valuesB : Values n)
    {A B deltaA deltaB : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (targetA targetB sampleA sampleB : Mixed n)
    (hCDF_A : CDFClose sampleA targetA deltaA) (hCDF_B : CDFClose sampleB targetB deltaB) :
    regret valuesA A sampleA sampleB ≤ regret valuesA A targetA targetB + deltaA + 2 * deltaB ∧
      regret valuesB B sampleB sampleA ≤ regret valuesB B targetB targetA + deltaB + 2 * deltaA :=
  both_regrets_stability valuesA valuesB hA hB
    (fun j t => by simpa only [abs_sub_comm] using hCDF_A j t)
    (fun j t => by simpa only [abs_sub_comm] using hCDF_B j t)

end Blotto
