import Blotto.PlayerSpecificFourInputEnvelopes
import Blotto.PlayerSpecificPolynomialPairTerms
import Blotto.PlayerSpecificFourReflectedPathSourceCost

/-! Complete reflected two-step resource path work is polynomial in the
incoming algebraic height and scalar midpoint precision. -/
namespace Blotto.PlayerSpecificFourReflectedPathEnvelope
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

private theorem resource_height : NaturalPolynomialEnvelope (fun U : ℕ => U)
    (fun U => PlayerSpecificResourceStepSizes.height U) := by
  refine ⟨8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+107,1,?_⟩
  intro U
  have h := PlayerSpecificResourceStepSizes.linear U
  simpa only [pow_one] using (Nat.le_trans (Nat.le_succ _) h)

theorem path_size : E
    (fun p => PlayerSpecificFourReflectedPathSourceCost.size p.1 p.2) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialPairTerms.first 16
  have hall := add (add hi PlayerSpecificPolynomialPairTerms.second) (c 3)
  simpa only [PlayerSpecificFourReflectedPathSourceCost.size] using hall

private theorem stepped_height : E (fun p =>
    PlayerSpecificResourceStepSizes.height
      (PlayerSpecificFourReflectedPathSourceCost.size p.1 p.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun U : ℕ => U)
    (g := fun p : ℕ × ℕ => PlayerSpecificFourReflectedPathSourceCost.size p.1 p.2)
    resource_height path_size

theorem work : E
    (fun p => PlayerSpecificFourReflectedPathSourceCost.work p.1 p.2) := by
  have h1 := PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ => p.1)
    PlayerSpecificFourInputEnvelopes.reflected_input
    PlayerSpecificPolynomialPairTerms.first
  have h2 := mul (c (4*PlayerSpecificResourceEntryPriceProfile.startCoefficient))
    (pow (add path_size (c 1)) 3)
  have h3 := mul (c (PlayerSpecificResourceBlockPolynomial.coefficient*3^3))
    (pow (add PlayerSpecificPolynomialPairTerms.second (c 1)) 3)
  have hframe := pow (add stepped_height (c 1)) 3
  have h4 := mul (c (3*PlayerSpecificFiniteResourceSourceCost.coefficient)) hframe
  have h5 := mul (c PlayerSpecificFiniteResourceSourceCost.frameCoefficient) hframe
  have hall := add (add (add (add (add h1 h2) h3) h4) h5) (c 2)
  simpa only [PlayerSpecificFourReflectedPathSourceCost.work] using hall

end Blotto.PlayerSpecificFourReflectedPathEnvelope
