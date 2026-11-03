import Blotto.PlayerSpecificTerminalCoreDrawEnvelope
import Blotto.PlayerSpecificTerminalCoreInputSourceCost

/-! The cached preparation and quotient construction have polynomial source work. -/
namespace Blotto.PlayerSpecificTerminalCoreInputEnvelope
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

theorem preparation_height : E (fun p =>
    PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2) := by
  have hbase := add
    (add (add (mul (add PlayerSpecificPolynomialPairTerms.second (c 1))
      (add PlayerSpecificPolynomialPairTerms.first PlayerSpecificPolynomialPairTerms.first))
      (c 3)) PlayerSpecificPolynomialPairTerms.second) (c 1)
  have hall := PlayerSpecificSourcePolynomialAutomation.step_envelope hbase
  simpa only [PlayerSpecificAlgebraicTerminalCorePreparationSizes.height] using hall

private theorem extra : E (fun p =>
    PlayerSpecificTerminalCoreInputSourceCost.extraWork p.2
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2) p.1) := by
  have h1 := mul
    (c (2*(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)))
    (pow (add PlayerSpecificPolynomialPairTerms.second (c 1)) 3)
  have h2 := mul
    (c (2618*PlayerSpecificResourceCostProfile.rationalCoefficient))
    (pow (add (add preparation_height PlayerSpecificPolynomialPairTerms.first) (c 7)) 3)
  have hall := add (add h1 h2) (c 2)
  change E (fun p =>
    2*(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(p.2+1)^3+
    (2618*PlayerSpecificResourceCostProfile.rationalCoefficient)*
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2+p.1+7)^3+2)
  exact hall

theorem work : E (fun p => PlayerSpecificTerminalCoreInputSourceCost.work p.1 p.2) := by
  have h1 := mul (mul
    (c PlayerSpecificTerminalPreparationPolynomial.coefficient)
    (pow (add PlayerSpecificPolynomialPairTerms.first (c 1)) 4))
    (pow (add PlayerSpecificPolynomialPairTerms.second (c 1)) 3)
  have hall := add (add h1 extra) (c 2)
  change E (fun p =>
    PlayerSpecificTerminalPreparationPolynomial.coefficient*(p.1+1)^4*(p.2+1)^3+
    PlayerSpecificTerminalCoreInputSourceCost.extraWork p.2
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2) p.1+2)
  exact hall

end Blotto.PlayerSpecificTerminalCoreInputEnvelope
