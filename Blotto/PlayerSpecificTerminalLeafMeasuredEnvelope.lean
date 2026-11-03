import Blotto.PlayerSpecificTerminalCoreMeasuredEnvelope
import Blotto.PlayerSpecificTerminalLeafEmissionPolynomial

/-! The reached terminal leaf includes original-coordinate emission. -/
namespace Blotto.PlayerSpecificTerminalLeafMeasuredEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialQuadrupleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k

private theorem emission : E (fun p =>
    PlayerSpecificTerminalLeafEmissionSourceCost.work p.1 p.2.1 p.2.2.2) := by
  have hp := mul
    (mul (c PlayerSpecificTerminalLeafEmissionPolynomial.coefficient)
      (pow (add PlayerSpecificPolynomialQuadrupleTerms.first (c 1)) 4))
    (pow (add (add PlayerSpecificPolynomialQuadrupleTerms.second
      PlayerSpecificPolynomialQuadrupleTerms.fourth) (c 1)) 3)
  apply NaturalPolynomialEnvelope.dominated hp
  intro p
  exact PlayerSpecificTerminalLeafEmissionPolynomial.work_polynomial p.1 p.2.1 p.2.2.2

theorem work : E (fun p =>
    PlayerSpecificTerminalLeafMeasuredSourceCost.work p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hall := add (add PlayerSpecificTerminalCoreMeasuredEnvelope.work emission) (c 2)
  change E (fun p =>
    PlayerSpecificTerminalCoreMeasuredSourceCost.work p.1 p.2.1 p.2.2.1 p.2.2.2+
    PlayerSpecificTerminalLeafEmissionSourceCost.work p.1 p.2.1 p.2.2.2+2)
  exact hall

end Blotto.PlayerSpecificTerminalLeafMeasuredEnvelope
