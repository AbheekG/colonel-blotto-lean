import Blotto.PlayerSpecificInitialMinimumEnvelope
import Blotto.PlayerSpecificFiniteSamplerPreparationPolynomial

/-! Complete public preparation source work is polynomial in dimension,
original rational input size and epsilon's binary word width. -/
namespace Blotto.PlayerSpecificFiniteSamplerPreparationEnvelope
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def size (p : ℕ × ℕ × ℚ) : ℕ := p.1+p.2.1+rationalWordWidth p.2.2
private abbrev E (f : ℕ × ℕ × ℚ → ℕ) := NaturalPolynomialEnvelope size f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℚ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℚ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ × ℚ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k
private theorem n : E (fun p => p.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
private theorem l : E (fun p => p.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
private theorem w : E (fun p => rationalWordWidth p.2.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

private theorem minimum : E (fun p => PlayerSpecificInitialMinimumCost.totalBound p.1 p.2.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (g := fun p : ℕ × ℕ × ℚ => (p.1,p.2.1))
    PlayerSpecificInitialMinimumEnvelope.work (add n l)

private theorem exponent : E (fun p =>
    PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) := by
  have h := mul (mul (c PlayerSpecificInitialPositivePrecision.coefficient)
    (add n (c 1))) (add l (c 1))
  simpa only [PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound] using h

theorem input_size : E (fun p =>
    PlayerSpecificFiniteAccuracySourcePolynomial.inputSize p.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2) := by
  have h := add (add (add n exponent) w) (c 1000)
  simpa only [PlayerSpecificFiniteAccuracySourcePolynomial.inputSize] using h

private theorem accuracy : E (fun p =>
    PlayerSpecificFiniteAccuracySourcePolynomial.polynomial p.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2) := by
  let q := fun p : ℕ × ℕ × ℚ =>
    PlayerSpecificFiniteAccuracySourcePolynomial.sizeBound p.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2
  let v := fun p : ℕ × ℕ × ℚ => 4*q p+40
  have hs : E q := by
    change E (fun p => 100*PlayerSpecificFiniteAccuracySourcePolynomial.inputSize p.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2)
    exact mul (c 100) input_size
  have hw : E v := add (mul (c 4) hs) (c 40)
  have hr : E (fun p => v p*v p+v p) :=
    add (mul hw hw) hw
  have h : E (fun p => 4000*(q p+1)*(v p*v p+v p)) :=
    mul (mul (c 4000) (add hs (c 1))) hr
  change E (fun p => 4000*(q p+1)*(v p*v p+v p))
  exact h

private theorem frame : E (fun p =>
    PlayerSpecificFiniteSamplerPreparationPolynomial.frameBound p.1 p.2.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2) := by
  have h := add (add (add
    (mul (c 3) l)
    (mul (add n (c 1000)) (mul (c 34) input_size)))
    (mul (c 100) input_size)) (c 100)
  simpa only [PlayerSpecificFiniteSamplerPreparationPolynomial.frameBound] using h

theorem work : E (fun p =>
    PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial p.1 p.2.1 p.2.2) := by
  have hrat := add (mul frame frame) frame
  have h := add (add (add minimum accuracy) (mul (c 27) hrat)) (c 2)
  change E (fun p =>
    PlayerSpecificInitialMinimumCost.totalBound p.1 p.2.1+
    PlayerSpecificFiniteAccuracySourcePolynomial.polynomial p.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2+
    27*(PlayerSpecificFiniteSamplerPreparationPolynomial.frameBound p.1 p.2.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2*
      PlayerSpecificFiniteSamplerPreparationPolynomial.frameBound p.1 p.2.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2+
      PlayerSpecificFiniteSamplerPreparationPolynomial.frameBound p.1 p.2.1
      (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound p.1 p.2.1) p.2.2)+2)
  exact h

end Blotto.PlayerSpecificFiniteSamplerPreparationEnvelope
