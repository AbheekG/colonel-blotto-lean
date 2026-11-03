import Blotto.PlayerSpecificOrderedFourDrawEnvelope
import Blotto.PlayerSpecificFourSpecDrawSourceCost

/-! The unsorted four-variable source draw includes sorting and output restoration. -/
namespace Blotto.PlayerSpecificFourSpecDrawEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev P := PlayerSpecificPolynomialPairTerms.size
private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem ordered_height_pair : NaturalPolynomialEnvelope P
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicOrderedFourDraw.height p.1 p.2) := by
  have hs := NaturalPolynomialEnvelope.add PlayerSpecificPolynomialPairTerms.sum
    (NaturalPolynomialEnvelope.constant P 1)
  have hm := NaturalPolynomialEnvelope.mul
    (NaturalPolynomialEnvelope.constant P PlayerSpecificAlgebraicOrderedFourDraw.coefficient) hs
  apply NaturalPolynomialEnvelope.dominated hm
  intro p
  have h := PlayerSpecificAlgebraicOrderedFourDraw.height_linear p.1 p.2
  omega

private theorem frame_height : E (fun p =>
    PlayerSpecificFourSpecDrawSourceCost.frameHeight p.1 p.2.2) := by
  have hh := PlayerSpecificPolynomialTripleTerms.lift_first_third ordered_height_pair
  have hmax := NaturalPolynomialEnvelope.max PlayerSpecificPolynomialTripleTerms.first hh
  have hall := add hmax (c 4)
  simpa only [PlayerSpecificFourSpecDrawSourceCost.frameHeight] using hall

private theorem input : E (fun p => PlayerSpecificFourSpecInputSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun T : ℕ => T)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    PlayerSpecificFourGuardEnvelope.spec_input_work PlayerSpecificPolynomialTripleTerms.first

theorem work : E (fun p =>
    PlayerSpecificFourSpecDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hf := NaturalPolynomialEnvelope.mul
    (c (1812*PlayerSpecificResourceCostProfile.rationalCoefficient))
    (NaturalPolynomialEnvelope.pow (add frame_height (c 1)) 3)
  have hall := add (add (add input PlayerSpecificOrderedFourDrawEnvelope.work) hf) (c 2)
  change E (fun p => PlayerSpecificFourSpecInputSourceCost.work p.1+
    PlayerSpecificOrderedFourDrawSourceCost.work p.1 p.2.1 p.2.2+
    (1812*PlayerSpecificResourceCostProfile.rationalCoefficient)*
      (PlayerSpecificFourSpecDrawSourceCost.frameHeight p.1 p.2.2+1)^3+2)
  exact hall

end Blotto.PlayerSpecificFourSpecDrawEnvelope
