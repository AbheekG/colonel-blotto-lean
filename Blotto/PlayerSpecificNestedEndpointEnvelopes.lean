import Blotto.PlayerSpecificNestedFirstTableEnvelope
import Blotto.PlayerSpecificNestedEndpointProfileSourceCost
import Blotto.PlayerSpecificNestedSecondUniformSourceCost
import Blotto.PlayerSpecificNestedTerminalPreparationSourceCost
import Blotto.PlayerSpecificNestedRestoreSourceCost

/-! Polynomial source work for nested endpoints, second uniform input,
terminal focus preparation and restoration. -/
namespace Blotto.PlayerSpecificNestedEndpointEnvelopes
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

private abbrev E (f : ℕ → ℕ) := NaturalPolynomialEnvelope (fun H : ℕ => H) f
private abbrev c := PlayerSpecificPolynomialTerms.constant
private theorem add {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H+g H) := NaturalPolynomialEnvelope.add hf hg

theorem endpoint_profile_work :
    E (fun H => PlayerSpecificNestedEndpointProfileSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 23 3
    PlayerSpecificNestedEndpointInputSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.stepped 1 3
    PlayerSpecificUnorderedThreeSourceCost.coefficient
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTerms.input 21
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    PlayerSpecificNestedDescriptorEnvelopes.pad_three_nine_nine hi
  have hall := add (add (add h1 h2) h3) (c 2)
  simpa only [PlayerSpecificNestedEndpointProfileSourceCost.work,iterate] using hall

theorem second_uniform_work :
    E (fun H => PlayerSpecificNestedSecondUniformSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 21 3
    PlayerSpecificNestedSecondInputSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.stepped 1 3
    PlayerSpecificOrderedThreeSourceCost.coefficient
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTerms.input 21
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    PlayerSpecificNestedDescriptorEnvelopes.shift_nine hi
  have hall := add (add (add h1 h2) h3) (c 2)
  simpa only [PlayerSpecificNestedSecondUniformSourceCost.work,iterate] using hall

theorem focus_work : E (fun H => PlayerSpecificNestedFocusSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificNestedFocusSourceCost.activeCoefficient
  have h2 := NaturalPolynomialEnvelope.mul (c 2) h1
  have hall := add h2 (c 7)
  simpa only [PlayerSpecificNestedFocusSourceCost.work,iterate] using hall

theorem terminal_endpoint_work :
    E (fun H => PlayerSpecificNestedTerminalEndpointSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 2
    PlayerSpecificAlgebraicEqualityCost.polynomialCoefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 0 6 3
    (1000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add h1 h2) (c 6)
  simpa only [PlayerSpecificNestedTerminalEndpointSourceCost.work,iterate] using hall

theorem terminal_preparation_work :
    E (fun H => PlayerSpecificNestedTerminalPreparationSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h2 := PlayerSpecificPolynomialTerms.stepped 21 3
    (4200*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add (add (add (add focus_work terminal_endpoint_work)
    terminal_endpoint_work) h1) h2) (c 40)
  simpa only [PlayerSpecificNestedTerminalPreparationSourceCost.work,iterate] using hall

theorem restore_work :
    E (fun H => PlayerSpecificNestedRestoreSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 6 3
    (1400*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add h1 (c 28)
  simpa only [PlayerSpecificNestedRestoreSourceCost.work,iterate] using hall

end Blotto.PlayerSpecificNestedEndpointEnvelopes
