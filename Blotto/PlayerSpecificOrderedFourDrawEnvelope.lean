import Blotto.PlayerSpecificFourGuardEnvelope
import Blotto.PlayerSpecificFourGluingDrawEnvelope
import Blotto.PlayerSpecificFourSmallDrawEnvelope
import Blotto.PlayerSpecificOrderedFourDrawSourceCost

/-! The complete ordered four-variable source draw has polynomial work. -/
namespace Blotto.PlayerSpecificOrderedFourDrawEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem guard : E (fun p => PlayerSpecificOrderedFourGuardSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun T : ℕ => T)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    PlayerSpecificFourGuardEnvelope.guard_work PlayerSpecificPolynomialTripleTerms.first

private theorem bit_frame : E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*((80*p.2.1+p.2.2)+p.2.2+1)^3) := by
  have h := add (add
    (add (NaturalPolynomialEnvelope.mul (c 80) PlayerSpecificPolynomialTripleTerms.second)
      PlayerSpecificPolynomialTripleTerms.third)
    PlayerSpecificPolynomialTripleTerms.third) (c 1)
  exact NaturalPolynomialEnvelope.mul (c PlayerSpecificBitSlicePolynomial.coefficient)
    (NaturalPolynomialEnvelope.pow h 3)

theorem work : E (fun p =>
    PlayerSpecificOrderedFourDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add (add guard bit_frame)
    PlayerSpecificFourGluingDrawEnvelope.work)
    PlayerSpecificFourSmallDrawEnvelope.work) (c 2)
  change E (fun p => PlayerSpecificOrderedFourGuardSourceCost.work p.1+
    PlayerSpecificBitSlicePolynomial.coefficient*((80*p.2.1+p.2.2)+p.2.2+1)^3+
    PlayerSpecificFourGluingDrawSourceCost.work p.1 p.2.1 p.2.2+
    PlayerSpecificFourSmallDrawSourceCost.work p.1 p.2.1 p.2.2+2)
  exact hall

end Blotto.PlayerSpecificOrderedFourDrawEnvelope
