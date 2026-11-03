import Blotto.PlayerSpecificTerminalLeafMeasuredEnvelope
import Blotto.PlayerSpecificResourceEntryInput

/-! Heights reached from the accepted rational finite sampler input. -/
namespace Blotto.PlayerSpecificFiniteInputHeightEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev E (f : ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k

private theorem cell : E (fun p => PlayerSpecificRecognitionInputHeights.cellHeight p.1 p.2) := by
  have h := mul (mul (c 10)
    (add PlayerSpecificPolynomialPairTerms.first (c 1)))
    (add PlayerSpecificPolynomialPairTerms.second (c 1))
  simpa only [PlayerSpecificRecognitionInputHeights.cellHeight] using h

private theorem parameter : E (fun p => PlayerSpecificFiniteParameterSizes.height p.1 p.2) := by
  have h := mul (c PlayerSpecificFiniteScaleHeights.coefficient) (add cell (c 1))
  simpa only [PlayerSpecificFiniteParameterSizes.height,
    PlayerSpecificFiniteParameterBudget.cellHeight] using h

private theorem initial : E (fun p => PlayerSpecificAlgebraicInitialInputSizes.height p.1 p.2) := by
  have hb := add (add parameter PlayerSpecificPolynomialPairTerms.second) (c 2)
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope hb 3
  simpa only [PlayerSpecificAlgebraicInitialInputSizes.height,
    PlayerSpecificAlgebraicInitialInputSizes.base,
    PlayerSpecificAlgebraicInitialHeights.height] using hi

private theorem path : E (fun p => PlayerSpecificAlgebraicPathContract.height p.1 p.2) := by
  have hl := mul (mul (c PlayerSpecificInitialLineageBound.coefficient)
    (pow (add PlayerSpecificPolynomialPairTerms.first (c 1)) 2))
    (add PlayerSpecificPolynomialPairTerms.second (c 1))
  have h := mul (c 3) (add hl (c 1))
  simpa only [PlayerSpecificAlgebraicPathContract.height,
    PlayerSpecificInitialLineageBound.height] using h

private theorem base : E (fun p => PlayerSpecificAlgebraicFiniteDrawContract.base p.1 p.2) := by
  have h := add (add (add (add parameter initial) path)
    PlayerSpecificPolynomialPairTerms.second) (c 2)
  simpa only [PlayerSpecificAlgebraicFiniteDrawContract.base] using h

theorem resource_entry : E (fun p => PlayerSpecificResourceEntryInput.height p.1 p.2) := by
  have h := add (add base PlayerSpecificPolynomialPairTerms.first) (c 1)
  simpa only [PlayerSpecificResourceEntryInput.height,
    PlayerSpecificOriginalResourceSourceCost.size] using h

end Blotto.PlayerSpecificFiniteInputHeightEnvelope
