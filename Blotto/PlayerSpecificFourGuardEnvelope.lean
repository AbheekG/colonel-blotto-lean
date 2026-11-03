import Blotto.PlayerSpecificPolynomialTerms
import Blotto.PlayerSpecificOrderedFourGuardSourceCost
import Blotto.PlayerSpecificFourSpecInputSourceCost

/-! Fixed-depth ordered-four guard and unsorted-four input work. -/
namespace Blotto.PlayerSpecificFourGuardEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

private abbrev E (f : ℕ → ℕ) := NaturalPolynomialEnvelope (fun T : ℕ => T) f
private abbrev c := PlayerSpecificPolynomialTerms.constant
private abbrev inp := PlayerSpecificPolynomialTerms.input
private theorem add {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun T => f T+g T) := NaturalPolynomialEnvelope.add hf hg

theorem threshold_height : E
    (fun T => PlayerSpecificOrderedFourGuardSourceCost.thresholdHeight T) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope inp 2
  have hbase := add (add (add hi (c 1)) (c 2)) (c 10)
  have hall := PlayerSpecificSourcePolynomialAutomation.iterate_envelope hbase 2
  simpa only [PlayerSpecificOrderedFourGuardSourceCost.thresholdHeight,
    PlayerSpecificExpressionVectorSourceCost.size,
    PlayerSpecificAlgebraicExpressionFixedCost.size] using hall

theorem guard_work : E
    (fun T => PlayerSpecificOrderedFourGuardSourceCost.work T) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 13 3
    PlayerSpecificMixtureScalarSourceCost.complementCoefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 2 14 3
    PlayerSpecificMixtureScalarSourceCost.scaleCoefficient
  have h3 := NaturalPolynomialEnvelope.mul
    (c PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient)
    (NaturalPolynomialEnvelope.pow (add threshold_height (c 1)) 3)
  have hall := add (add (add h1 h2) h3) (c 2)
  simpa only [PlayerSpecificOrderedFourGuardSourceCost.work,iterate] using hall

theorem spec_input_work : E
    (fun T => PlayerSpecificFourSpecInputSourceCost.work T) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 2 3
    PlayerSpecificSortTripleSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 0 7 3
    (2609*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add h1 h2) (c 2)
  simpa only [PlayerSpecificFourSpecInputSourceCost.work,iterate] using hall

end Blotto.PlayerSpecificFourGuardEnvelope
