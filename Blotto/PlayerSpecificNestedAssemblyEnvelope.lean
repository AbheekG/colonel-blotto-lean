import Blotto.PlayerSpecificNestedProfileHeightsEnvelope
import Blotto.PlayerSpecificNestedDescriptorEnvelopes

/-! Polynomial source work of the fixed descriptor operations at the
reached third-case assembly height. -/
namespace Blotto.PlayerSpecificNestedAssemblyEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev A := PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight

theorem binary_work : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificDescriptorBinarySourceCost.work (A p.1 p.2) 3 9 9) := by
  exact PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (f := fun H => PlayerSpecificDescriptorBinarySourceCost.work H 3 9 9)
    (g := fun p : ℕ × ℕ => A p.1 p.2)
    PlayerSpecificNestedDescriptorEnvelopes.binary_three_nine_nine
    PlayerSpecificNestedProfileHeightsEnvelope.third_assembly_height

theorem pad_work : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificDescriptorPadSourceCost.work (A p.1 p.2) 3 9 9) := by
  exact PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (f := fun H => PlayerSpecificDescriptorPadSourceCost.work H 3 9 9)
    (g := fun p : ℕ × ℕ => A p.1 p.2)
    PlayerSpecificNestedDescriptorEnvelopes.pad_three_nine_nine
    PlayerSpecificNestedProfileHeightsEnvelope.third_assembly_height

end Blotto.PlayerSpecificNestedAssemblyEnvelope
