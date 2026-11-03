import Blotto.PlayerSpecificNestedLeafEnvelopes
import Blotto.PlayerSpecificNestedDescriptorEnvelopes

/-! The complete first nested conditional table preparation has a
polynomial source-work envelope at its reached input height. -/
namespace Blotto.PlayerSpecificNestedFirstTableEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem geometry_work :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => PlayerSpecificNestedGeometrySourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 22 3
    PlayerSpecificNestedParameterSourceCost.firstCoefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 4 27 3
    PlayerSpecificThreeGeometrySourceCost.coefficient
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTerms.input 21
  have h3 := PlayerSpecificPolynomialSubstitution.substitute
    PlayerSpecificNestedDescriptorEnvelopes.shift_nine hi
  have h := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add
      (NaturalPolynomialEnvelope.add h1 h2) h3)
    (PlayerSpecificPolynomialTerms.constant 2)
  simpa only [PlayerSpecificNestedGeometrySourceCost.work,iterate] using h

theorem first_table_work :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => PlayerSpecificNestedFirstTableSourceCost.work H) := by
  have h := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add
      (NaturalPolynomialEnvelope.add
        PlayerSpecificNestedLeafEnvelopes.positive_work geometry_work)
      PlayerSpecificNestedLeafEnvelopes.zero_work)
    (PlayerSpecificPolynomialTerms.constant 2)
  simpa only [PlayerSpecificNestedFirstTableSourceCost.work] using h

end Blotto.PlayerSpecificNestedFirstTableEnvelope
