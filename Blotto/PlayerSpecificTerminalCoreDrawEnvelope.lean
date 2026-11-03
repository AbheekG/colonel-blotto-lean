import Blotto.PlayerSpecificTerminalCoreSelectedEnvelope
import Blotto.PlayerSpecificTerminalCoreDrawSourceCost

/-! The complete terminal core adds its original-coordinate output frame. -/
namespace Blotto.PlayerSpecificTerminalCoreDrawEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev P := PlayerSpecificPolynomialPairTerms.size
private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem output_height_pair : NaturalPolynomialEnvelope P
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicTerminalCoreDrawBounds.height p.1 p.2) := by
  have hs := NaturalPolynomialEnvelope.add PlayerSpecificPolynomialPairTerms.sum
    (NaturalPolynomialEnvelope.constant P 1)
  have hm := NaturalPolynomialEnvelope.mul
    (NaturalPolynomialEnvelope.constant P PlayerSpecificAlgebraicTerminalCoreDrawBounds.coefficient) hs
  apply NaturalPolynomialEnvelope.dominated hm
  intro p
  have h := PlayerSpecificAlgebraicTerminalCoreDrawBounds.height_linear p.1 p.2
  omega

private theorem frame_height : E (fun p =>
    PlayerSpecificTerminalCoreDrawSourceCost.frameHeight p.1 p.2.2) := by
  have hh := PlayerSpecificPolynomialTripleTerms.lift_first_third output_height_pair
  have hmax := NaturalPolynomialEnvelope.max PlayerSpecificPolynomialTripleTerms.first hh
  have hall := add hmax (c 6)
  simpa only [PlayerSpecificTerminalCoreDrawSourceCost.frameHeight] using hall

theorem work : E (fun p =>
    PlayerSpecificTerminalCoreDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hf := NaturalPolynomialEnvelope.mul
    (c (2206*PlayerSpecificResourceCostProfile.rationalCoefficient))
    (NaturalPolynomialEnvelope.pow (add frame_height (c 1)) 3)
  have hall := add (add PlayerSpecificTerminalCoreSelectedEnvelope.work hf) (c 2)
  change E (fun p => PlayerSpecificTerminalCoreSelectedSourceCost.work p.1 p.2.1 p.2.2+
    (2206*PlayerSpecificResourceCostProfile.rationalCoefficient)*
      (PlayerSpecificTerminalCoreDrawSourceCost.frameHeight p.1 p.2.2+1)^3+2)
  exact hall

end Blotto.PlayerSpecificTerminalCoreDrawEnvelope
