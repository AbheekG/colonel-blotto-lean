import Blotto.PlayerSpecificRationalOutputEnvelope

/-! Original-input rational-output work after algebraic draw and output rounding. -/
namespace Blotto.PlayerSpecificRationalFiniteOutputEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 1024

private abbrev S := PlayerSpecificPolynomialQuadrupleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k

private theorem output_height : E (fun p =>
    PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient*(p.1+1)^3*
      (p.2.1+p.2.2.1+p.1+1)) := by
  exact mul (mul (c PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient)
    (pow (add PlayerSpecificPolynomialQuadrupleTerms.first (c 1)) 3))
    (add (add (add PlayerSpecificPolynomialQuadrupleTerms.second
      PlayerSpecificPolynomialQuadrupleTerms.third)
      PlayerSpecificPolynomialQuadrupleTerms.first) (c 1))

attribute [local irreducible] PlayerSpecificRationalOutputSourcePolynomial.polynomial
  PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient

private theorem compose {g : ℕ × ℕ × ℕ × ℕ → ℕ} (hg : E g) :
    E (fun p => 2*PlayerSpecificRationalOutputSourcePolynomial.polynomial
      p.1 (g p) p.2.2.2) := by
  have hs := add (add PlayerSpecificPolynomialQuadrupleTerms.first hg)
    PlayerSpecificPolynomialQuadrupleTerms.fourth
  have hp := PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := PlayerSpecificRationalOutputEnvelope.size)
    (g := fun p : ℕ × ℕ × ℕ × ℕ => (p.1,g p,p.2.2.2))
    PlayerSpecificRationalOutputEnvelope.polynomial hs
  exact mul (c 2) hp

theorem work : E (fun p =>
    2*PlayerSpecificRationalOutputSourcePolynomial.polynomial p.1
      (PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient*(p.1+1)^3*
        (p.2.1+p.2.2.1+p.1+1)) p.2.2.2) :=
  compose output_height

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) :
    ∃ C d : ℕ, ∀ K P,
      PlayerSpecificRationalFiniteOutputPolynomial.outputWork i K P ≤
        C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+K+P+1)^d := by
  obtain ⟨C,d,h⟩ := work
  refine ⟨C,d,?_⟩
  intro K P
  exact h (N,PlayerSpecificInitialPositivePrecision.inputSize i,K,P)

end Blotto.PlayerSpecificRationalFiniteOutputEnvelope
