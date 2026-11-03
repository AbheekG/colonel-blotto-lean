import Blotto.PlayerSpecificPolynomialTripleTerms
import Blotto.PlayerSpecificNestedClosedProfileEnvelope
import Blotto.PlayerSpecificNestedSpecDrawSourceCost

/-! The complete closed-probability nested draw source expression has a
polynomial bound in raw row height and both finite-bit precisions. -/
namespace Blotto.PlayerSpecificNestedSpecDrawEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem packet : E (fun p =>
    PlayerSpecificNestedPacketSourceCost.coefficient*
      (PlayerSpecificNestedPacketSourceCost.size 18 p.2.1 p.2.2+1)^3) :=
  PlayerSpecificPolynomialTripleTerms.lift_second_third
    PlayerSpecificPolynomialPairTerms.nested_packet_work

private theorem profile : E (fun p =>
    PlayerSpecificNestedSpecProfileSourceCost.work p.1 p.2.2) :=
  PlayerSpecificPolynomialTripleTerms.lift_first_third
    PlayerSpecificNestedClosedProfileEnvelope.spec_profile_work

private theorem interior_height : E (fun p =>
    PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2.2) :=
  PlayerSpecificPolynomialTripleTerms.lift_first_third
    PlayerSpecificNestedProfileHeightsEnvelope.interior_profile_height

private theorem frame_height : E (fun p =>
    PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2.2+
      3+18+p.2.1+p.2.2+1) :=
  add (add (add (add (add interior_height (c 3)) (c 18))
    PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third) (c 1)

private theorem segment_work : E (fun p =>
    PlayerSpecificSegmentDrawSourceCost.coefficient*
      (PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2.2+
        3+18+p.2.1+p.2.2+1)^16) :=
  NaturalPolynomialEnvelope.mul
    (c PlayerSpecificSegmentDrawSourceCost.coefficient)
    (NaturalPolynomialEnvelope.pow frame_height 16)

theorem work : E (fun p => PlayerSpecificNestedSpecDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add packet profile) segment_work) (c 2)
  simpa only [PlayerSpecificNestedSpecDrawSourceCost.work] using hall

end Blotto.PlayerSpecificNestedSpecDrawEnvelope
