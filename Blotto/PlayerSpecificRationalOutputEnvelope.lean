import Blotto.PlayerSpecificFiniteSamplerPreparationEnvelope
import Blotto.PlayerSpecificRationalFiniteOutputPolynomial

/-! Dyadic rational-output source polynomial as an envelope in count,
algebraic row height, and output precision. -/
namespace Blotto.PlayerSpecificRationalOutputEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def size (p : ℕ × ℕ × ℕ) : ℕ := p.1+p.2.1+p.2.2
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope size f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem n : E (fun p => p.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
private theorem t : E (fun p => p.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)
private theorem precision : E (fun p => p.2.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro p; dsimp [size]; omega)

private def packet (p : ℕ × ℕ × ℕ) : ℕ := p.2.1+p.2.2+5
private def height (p : ℕ × ℕ × ℕ) : ℕ :=
  PlayerSpecificAlgebraicHeightEnvelope.coefficient*packet p
private def rate (u : ℕ) : ℕ :=
  let w := PlayerSpecificAlgebraicComparisonCost.widthCoefficient*(u+1)
  w*w+w
private def predicate (p : ℕ × ℕ × ℕ) : ℕ :=
  (256*packet p+8000000408+
    PlayerSpecificAlgebraicComparisonExecution.coefficient*(height p+1))*rate (height p)
private def search (p : ℕ × ℕ × ℕ) : ℕ :=
  packet p*(predicate p+150*rate (height p))+(256*packet p+157)*rate (height p)
private def round (p : ℕ × ℕ × ℕ) : ℕ :=
  search p+(256*packet p+278)*rate (height p)
private def raw (p : ℕ × ℕ × ℕ) : ℕ :=
  p.1*round p+(141+138*p.1)*rate (height p+p.1+6)

private theorem hp : E packet := by
  have h := add (add t precision) (c 5)
  change E (fun p => p.2.1+p.2.2+5)
  exact h
private theorem hu : E height := by
  have h := mul (c PlayerSpecificAlgebraicHeightEnvelope.coefficient) hp
  change E (fun p => PlayerSpecificAlgebraicHeightEnvelope.coefficient*packet p)
  exact h
private theorem hr {u : ℕ × ℕ × ℕ → ℕ} (h : E u) : E (fun p => rate (u p)) := by
  have hw := mul (c PlayerSpecificAlgebraicComparisonCost.widthCoefficient)
    (add h (c 1))
  have hall := add (mul hw hw) hw
  change E (fun p =>
    (PlayerSpecificAlgebraicComparisonCost.widthCoefficient*(u p+1))*
      (PlayerSpecificAlgebraicComparisonCost.widthCoefficient*(u p+1))+
    PlayerSpecificAlgebraicComparisonCost.widthCoefficient*(u p+1))
  exact hall
private theorem hpredicate : E predicate := by
  have ha := add (add (mul (c 256) hp) (c 8000000408))
    (mul (c PlayerSpecificAlgebraicComparisonExecution.coefficient) (add hu (c 1)))
  have hall := mul ha (hr hu)
  change E (fun p =>
    (256*packet p+8000000408+
      PlayerSpecificAlgebraicComparisonExecution.coefficient*(height p+1))*rate (height p))
  exact hall
private theorem hsearch : E search := by
  have h := add
    (mul hp (add hpredicate (mul (c 150) (hr hu))))
    (mul (add (mul (c 256) hp) (c 157)) (hr hu))
  change E (fun p =>
    packet p*(predicate p+150*rate (height p))+(256*packet p+157)*rate (height p))
  exact h
private theorem hround : E round := by
  have h := add hsearch
    (mul (add (mul (c 256) hp) (c 278)) (hr hu))
  change E (fun p => search p+(256*packet p+278)*rate (height p))
  exact h
private theorem hraw : E raw := by
  have h := add (mul n hround)
    (mul (add (c 141) (mul (c 138) n))
      (hr (add (add hu n) (c 6))))
  change E (fun p => p.1*round p+(141+138*p.1)*rate (height p+p.1+6))
  exact h

theorem polynomial : E (fun p =>
    PlayerSpecificRationalOutputSourcePolynomial.polynomial p.1 p.2.1 p.2.2) := by
  change E raw
  exact hraw

end Blotto.PlayerSpecificRationalOutputEnvelope
