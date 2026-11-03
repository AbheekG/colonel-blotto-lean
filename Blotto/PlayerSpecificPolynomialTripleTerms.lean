import Blotto.PlayerSpecificPolynomialPairTerms

/-! Polynomial source-size projections for row height and two bit
precision parameters. -/
namespace Blotto.PlayerSpecificPolynomialTripleTerms
set_option autoImplicit false

def size (p : ℕ × ℕ × ℕ) : ℕ := p.1+p.2.1+p.2.2

theorem first : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => p.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem second : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => p.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem third : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => p.2.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem first_third : NaturalPolynomialEnvelope size
    (fun p : ℕ × ℕ × ℕ => p.1+p.2.2) :=
  NaturalPolynomialEnvelope.add first third

theorem first_second : NaturalPolynomialEnvelope size
    (fun p : ℕ × ℕ × ℕ => p.1+p.2.1) :=
  NaturalPolynomialEnvelope.add first second

theorem second_third : NaturalPolynomialEnvelope size
    (fun p : ℕ × ℕ × ℕ => p.2.1+p.2.2) :=
  NaturalPolynomialEnvelope.add second third

theorem lift_first_third {f : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope PlayerSpecificPolynomialPairTerms.size f) :
    NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => f (p.1,p.2.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (g := fun p : ℕ × ℕ × ℕ => (p.1,p.2.2)) hf first_third

theorem lift_second_third {f : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope PlayerSpecificPolynomialPairTerms.size f) :
    NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => f (p.2.1,p.2.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (g := fun p : ℕ × ℕ × ℕ => (p.2.1,p.2.2)) hf second_third

theorem lift_first_second {f : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope PlayerSpecificPolynomialPairTerms.size f) :
    NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ => f (p.1,p.2.1)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (g := fun p : ℕ × ℕ × ℕ => (p.1,p.2.1)) hf first_second

end Blotto.PlayerSpecificPolynomialTripleTerms
