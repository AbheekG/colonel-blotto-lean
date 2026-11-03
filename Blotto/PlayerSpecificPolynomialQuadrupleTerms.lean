import Blotto.PlayerSpecificTerminalCoreInputEnvelope

/-! Polynomial source-size projections for field count, row height, and two precisions. -/
namespace Blotto.PlayerSpecificPolynomialQuadrupleTerms
set_option autoImplicit false

def size (p : ℕ × ℕ × ℕ × ℕ) : ℕ := p.1+p.2.1+p.2.2.1+p.2.2.2

theorem first : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ × ℕ => p.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
theorem second : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
theorem third : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
theorem fourth : NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

theorem lift_first_second {f : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope PlayerSpecificPolynomialPairTerms.size f) :
    NaturalPolynomialEnvelope size (fun p : ℕ × ℕ × ℕ × ℕ => f (p.1,p.2.1)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (g := fun p : ℕ × ℕ × ℕ × ℕ => (p.1,p.2.1)) hf
    (NaturalPolynomialEnvelope.add first second)

theorem lift_first_third_fourth {f : ℕ × ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope PlayerSpecificPolynomialTripleTerms.size f) :
    NaturalPolynomialEnvelope size
      (fun p : ℕ × ℕ × ℕ × ℕ => f (p.1,p.2.2.1,p.2.2.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialTripleTerms.size)
    (g := fun p : ℕ × ℕ × ℕ × ℕ => (p.1,p.2.2.1,p.2.2.2)) hf
    (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add first third) fourth)

end Blotto.PlayerSpecificPolynomialQuadrupleTerms
