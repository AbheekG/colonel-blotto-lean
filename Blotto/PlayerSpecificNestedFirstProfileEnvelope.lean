import Blotto.PlayerSpecificNestedProfileHeightsEnvelope
import Blotto.PlayerSpecificNestedFirstTableEnvelope
import Blotto.PlayerSpecificNestedEndpointEnvelopes
import Blotto.PlayerSpecificNestedProfileSourceCost

/-! Full first and family nested profile source work is polynomial in raw
row height and scalar midpoint precision. -/
namespace Blotto.PlayerSpecificNestedFirstProfileEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private theorem c (n : ℕ) : NaturalPolynomialEnvelope S (fun _ => n) :=
  NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope S f)
    (hg : NaturalPolynomialEnvelope S g) :
    NaturalPolynomialEnvelope S (fun p => f p+g p) :=
  NaturalPolynomialEnvelope.add hf hg

theorem first_profile_work : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedFirstProfileSourceCost.work p.1 p.2) := by
  have h2 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => PlayerSpecificNestedFirstProfileSourceCost.locationHeight p.1 p.2)
    PlayerSpecificNestedFirstTableEnvelope.first_table_work
    PlayerSpecificNestedProfileHeightsEnvelope.first_location_height
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => PlayerSpecificNestedFirstProfileSourceCost.tableHeight p.1 p.2)
    PlayerSpecificNestedDescriptorEnvelopes.pad_three_nine_nine
    PlayerSpecificNestedProfileHeightsEnvelope.first_table_height
  have hall := add (add (add PlayerSpecificPolynomialPairTerms.nested_location_work h2) h3) (c 2)
  simpa only [PlayerSpecificNestedFirstProfileSourceCost.work] using hall

private theorem family_location_size : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => iterate 9 p.1+p.2) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialPairTerms.first 9
  exact add hi PlayerSpecificPolynomialPairTerms.second

theorem family_location_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedProfileSourceCost.locationHeight p.1 p.2) := by
  have h := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => (iterate 9 p.1,p.2))
    PlayerSpecificNestedProfileHeightsEnvelope.first_location_height family_location_size
  simpa only [PlayerSpecificNestedProfileSourceCost.locationHeight,
    PlayerSpecificNestedFirstProfileSourceCost.locationHeight] using h

theorem family_profile_work : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedProfileSourceCost.work p.1 p.2) := by
  have h1 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => p.1)
    PlayerSpecificNestedLeafEnvelopes.family_work PlayerSpecificPolynomialPairTerms.first
  have h2 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => (iterate 9 p.1,p.2))
    PlayerSpecificPolynomialPairTerms.nested_location_work family_location_size
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => PlayerSpecificNestedProfileSourceCost.locationHeight p.1 p.2)
    PlayerSpecificNestedFirstTableEnvelope.first_table_work family_location_height
  have hall := add (add (add h1 h2) h3) (c 2)
  simpa only [PlayerSpecificNestedProfileSourceCost.work] using hall

end Blotto.PlayerSpecificNestedFirstProfileEnvelope
