import Blotto.PlayerSpecificPolynomialTerms
import Blotto.PlayerSpecificFourReflectedInputSourceCost
import Blotto.PlayerSpecificFourMergedInputSourceCost
import Blotto.PlayerSpecificFourReflectedTerminalSourceCost
import Blotto.PlayerSpecificReflectAppendSourceCost

/-! Fixed-depth four-branch input and restoration source work has
polynomial envelopes at every reached row height. -/
namespace Blotto.PlayerSpecificFourInputEnvelopes
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

private abbrev E (f : ℕ → ℕ) := NaturalPolynomialEnvelope (fun H : ℕ => H) f
private abbrev c := PlayerSpecificPolynomialTerms.constant
private theorem add {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H+g H) := NaturalPolynomialEnvelope.add hf hg

theorem reflected_input : E
    (fun H => PlayerSpecificFourReflectedInputSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 25 3
    PlayerSpecificFourParameterSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 13 14 3
    (3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient)
  have h3 := PlayerSpecificPolynomialTerms.iterated 14 14 3
    (3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient)
  have h4 := PlayerSpecificPolynomialTerms.iterated 15 21 3
    (4600*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add (add (add (add h1 h2) h2) h3) h4) (c 32)
  simpa only [PlayerSpecificFourReflectedInputSourceCost.work,iterate] using hall

theorem merged_input : E
    (fun H => PlayerSpecificFourMergedInputSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 25 3
    PlayerSpecificFourParameterSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 13 14 3
    PlayerSpecificMixtureScalarSourceCost.scaleCoefficient
  have h3 := PlayerSpecificPolynomialTerms.iterated 14 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h4 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h5 := PlayerSpecificPolynomialTerms.iterated 15 11 3
    (2800*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add (add (add (add (add (add h1 h2) h2) h2) h3) h4) h5) (c 24)
  simpa only [PlayerSpecificFourMergedInputSourceCost.work,iterate] using hall

theorem reflected_terminal : E
    (fun H => PlayerSpecificFourReflectedTerminalSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 16 21 3
    (6000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add h1 (c 28)
  simpa only [PlayerSpecificFourReflectedTerminalSourceCost.work] using hall

theorem reflect_append : E
    (fun H => PlayerSpecificReflectAppendSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (3*(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient))
  have h2 := PlayerSpecificPolynomialTerms.stepped 11 3
    (2200*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add h1 h2) (c 16)
  simpa only [PlayerSpecificReflectAppendSourceCost.work,iterate] using hall

end Blotto.PlayerSpecificFourInputEnvelopes
