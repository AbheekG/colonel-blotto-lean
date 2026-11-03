import Blotto.PlayerSpecificPolynomialSubstitution

/-! Reusable monomial witnesses for fixed-height source-cost terms. -/
namespace Blotto.PlayerSpecificPolynomialTerms
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false

theorem input : NaturalPolynomialEnvelope (fun H : ℕ => H) (fun H => H) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro H; exact le_rfl)

theorem iterated (k offset power C : ℕ) :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => C*(iterate k H+offset)^power) :=
  NaturalPolynomialEnvelope.mul
    (NaturalPolynomialEnvelope.constant _ C)
    (NaturalPolynomialEnvelope.pow
      (NaturalPolynomialEnvelope.add
        (PlayerSpecificSourcePolynomialAutomation.iterate_envelope input k)
        (NaturalPolynomialEnvelope.constant _ offset)) power)

theorem constant (C : ℕ) :
    NaturalPolynomialEnvelope (fun H : ℕ => H) (fun _ => C) :=
  NaturalPolynomialEnvelope.constant _ C

theorem stepped (offset power C : ℕ) :
    NaturalPolynomialEnvelope (fun H : ℕ => H)
      (fun H => C*(step H+offset)^power) :=
  NaturalPolynomialEnvelope.mul
    (constant C)
    (NaturalPolynomialEnvelope.pow
      (NaturalPolynomialEnvelope.add
        (PlayerSpecificSourcePolynomialAutomation.step_envelope input)
        (constant offset)) power)

end Blotto.PlayerSpecificPolynomialTerms
