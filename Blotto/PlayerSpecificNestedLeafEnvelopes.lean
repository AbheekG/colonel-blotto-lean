import Blotto.PlayerSpecificPolynomialSubstitution
import Blotto.PlayerSpecificNestedFirstTableSourceCost
import Blotto.PlayerSpecificNestedFamilySourceCost

/-! Polynomial envelopes for three fixed-depth nested source leaves.
The common witness constructor keeps the large absolute coefficients opaque. -/
namespace Blotto.PlayerSpecificNestedLeafEnvelopes
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

private theorem input : NaturalPolynomialEnvelope (fun H : ℕ => H) (fun H => H) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro H; exact le_rfl)

private theorem iterated_term (k offset power C : ℕ) :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => C*(iterate k H+offset)^power) :=
  NaturalPolynomialEnvelope.mul
    (NaturalPolynomialEnvelope.constant _ C)
    (NaturalPolynomialEnvelope.pow
      (NaturalPolynomialEnvelope.add
        (PlayerSpecificSourcePolynomialAutomation.iterate_envelope input k)
        (NaturalPolynomialEnvelope.constant _ offset)) power)

theorem positive_work :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => PlayerSpecificNestedPositiveSourceCost.work H) := by
  have h1 := iterated_term 0 19 3 PlayerSpecificNestedParameterSourceCost.scalarCoefficient
  have h2 := iterated_term 9 11 3
    (PlayerSpecificAlgebraicComparisonExecution.coefficient*
      PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add h1 h2)
    (NaturalPolynomialEnvelope.constant (fun H : ℕ => H) 2)
  simpa only [PlayerSpecificNestedPositiveSourceCost.work,iterate] using h

theorem zero_work :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => PlayerSpecificNestedZeroSourceCost.work H) := by
  have h1 := iterated_term 0 27 3 PlayerSpecificNestedZeroSourceCost.weightsCoefficient
  have h2 := iterated_term 22 20 5 PlayerSpecificDescriptorCopySourceCost.coefficient
  have h := NaturalPolynomialEnvelope.add h1 h2
  simpa only [PlayerSpecificNestedZeroSourceCost.work,iterate] using h

theorem family_work :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => PlayerSpecificNestedFamilySourceCost.work H) := by
  have h1 := iterated_term 0 19 3 PlayerSpecificNestedParameterSourceCost.scalarCoefficient
  have h2 := iterated_term 9 11 3
    (3000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add h1 h2)
    (NaturalPolynomialEnvelope.constant (fun H : ℕ => H) 12)
  simpa only [PlayerSpecificNestedFamilySourceCost.work,iterate] using h

end Blotto.PlayerSpecificNestedLeafEnvelopes
