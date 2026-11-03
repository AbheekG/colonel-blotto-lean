import Blotto.PlayerSpecificNestedRemainingProfilesEnvelope
import Blotto.PlayerSpecificNestedSortedProfileSourceCost
import Blotto.PlayerSpecificNestedSpecProfileSourceCost

/-! Complete closed-probability nested profile source work, including the
zero/one endpoint tests, sorting and interior selected-case dispatch. -/
namespace Blotto.PlayerSpecificNestedClosedProfileEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev E (f : ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem lift_first {f : ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope (fun H : ℕ => H) f) :
    E (fun p => f p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ => p.1) hf PlayerSpecificPolynomialPairTerms.first

theorem sorted_input_work : NaturalPolynomialEnvelope (fun H : ℕ => H)
    (fun H => PlayerSpecificNestedSortedProfileSourceCost.inputWork H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificCompareSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 0 11 3
    (3000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add h1 h2)
    (PlayerSpecificPolynomialTerms.constant 14)
  simpa only [PlayerSpecificNestedSortedProfileSourceCost.inputWork,iterate] using hall

theorem sorted_work : E
    (fun p => PlayerSpecificNestedSortedProfileSourceCost.work p.1 p.2) := by
  have h1 := lift_first sorted_input_work
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (f := fun H => PlayerSpecificDescriptorSwapSourceCost.work H 18)
    (g := fun p : ℕ × ℕ => PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2)
    PlayerSpecificNestedDescriptorEnvelopes.swap_eighteen
    PlayerSpecificNestedProfileHeightsEnvelope.interior_profile_height
  have hall := add (add (add h1
    PlayerSpecificNestedRemainingProfilesEnvelope.interior_profile_work) h3) (c 2)
  simpa only [PlayerSpecificNestedSortedProfileSourceCost.work] using hall

theorem q_one_work : NaturalPolynomialEnvelope (fun H : ℕ => H)
    (fun H => PlayerSpecificNestedSpecProfileSourceCost.qOneWork H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h2 := PlayerSpecificPolynomialTerms.stepped 1 3
    PlayerSpecificCompareSourceCost.coefficient
  have hall := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add h1 h2)
    (PlayerSpecificPolynomialTerms.constant 2)
  simpa only [PlayerSpecificNestedSpecProfileSourceCost.qOneWork,iterate] using hall

theorem spec_profile_work : E
    (fun p => PlayerSpecificNestedSpecProfileSourceCost.work p.1 p.2) := by
  have hc := lift_first (PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificCompareSourceCost.coefficient)
  have ho := lift_first q_one_work
  have he := lift_first PlayerSpecificNestedEndpointEnvelopes.endpoint_profile_work
  have hall := add (add (add (add (add hc ho) he) he) sorted_work) (c 4)
  simpa only [PlayerSpecificNestedSpecProfileSourceCost.work,iterate] using hall

end Blotto.PlayerSpecificNestedClosedProfileEnvelope
