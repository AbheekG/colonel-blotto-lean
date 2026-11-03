import Blotto.PlayerSpecificPolynomialTerms
import Blotto.PlayerSpecificNestedLocationSourcePolynomial
import Blotto.PlayerSpecificNestedPacketSourcePolynomial

/-! Common two-parameter polynomial envelopes for source-cost composition. -/
namespace Blotto.PlayerSpecificPolynomialPairTerms
set_option autoImplicit false

def size (p : ℕ × ℕ) : ℕ := p.1+p.2

theorem first : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ => p.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem second : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ => p.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem sum : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ => p.1+p.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; exact le_rfl)

theorem nested_location_work :
    NaturalPolynomialEnvelope size
      (fun p : ℕ × ℕ => PlayerSpecificNestedLocationSourceCost.work p.1 p.2) := by
  let C := PlayerSpecificNestedLocationSourcePolynomial.coefficient
  refine ⟨C*5^3,3,?_⟩
  intro p
  have h := PlayerSpecificNestedLocationSourcePolynomial.work_bound p.1 p.2
  have hs : p.1+p.2+5≤5*(size p+1) := by dsimp [size]; omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs 3)
  calc
    PlayerSpecificNestedLocationSourceCost.work p.1 p.2 ≤ C*(p.1+p.2+5)^3 := h
    _ ≤ C*(5*(size p+1))^3 := hp
    _ = (C*5^3)*(size p+1)^3 := by ring

theorem nested_packet_work :
    NaturalPolynomialEnvelope size
      (fun p : ℕ × ℕ => PlayerSpecificNestedPacketSourceCost.coefficient*
        (PlayerSpecificNestedPacketSourceCost.size 18 p.1 p.2+1)^3) := by
  refine ⟨PlayerSpecificNestedPacketSourceCost.coefficient*29^3,3,?_⟩
  intro p
  simpa only [size] using PlayerSpecificNestedPacketSourcePolynomial.work_bound p.1 p.2

end Blotto.PlayerSpecificPolynomialPairTerms
