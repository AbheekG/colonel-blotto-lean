import Blotto.PlayerSpecificFourMergedDrawEnvelope
import Blotto.PlayerSpecificFourReflectedDrawEnvelope
import Blotto.PlayerSpecificFourSmallDrawSourceCost

/-! The complete small four-variable source draw is polynomial in the
incoming height and both random-bit precisions. -/
namespace Blotto.PlayerSpecificFourSmallDrawEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k

private theorem remaining : E (fun p =>
    PlayerSpecificAlgebraicFourSmallDraw.remaining p.2.1 p.2.2) := by
  have h2 := mul (c 2) PlayerSpecificPolynomialTripleTerms.second
  have h17 := mul (c 17) PlayerSpecificPolynomialTripleTerms.second
  have hall := add h2 (add (add h17 PlayerSpecificPolynomialTripleTerms.third)
    PlayerSpecificPolynomialTripleTerms.third)
  simpa only [PlayerSpecificAlgebraicFourSmallDraw.remaining] using hall

private theorem bit_count : E (fun p =>
    PlayerSpecificAlgebraicFourSmallDraw.bitCount p.2.1 p.2.2) := by
  have hall := add PlayerSpecificPolynomialTripleTerms.second remaining
  simpa only [PlayerSpecificAlgebraicFourSmallDraw.bitCount] using hall

private theorem slice_bits : E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicFourSmallDraw.bitCount p.2.1 p.2.2+1)^3) :=
  mul (c PlayerSpecificBitSlicePolynomial.coefficient)
    (pow (add bit_count (c 1)) 3)

private theorem slice_remaining : E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicFourSmallDraw.remaining p.2.1 p.2.2+1)^3) :=
  mul (c PlayerSpecificBitSlicePolynomial.coefficient)
    (pow (add remaining (c 1)) 3)

private theorem coin_work : E (fun p =>
    PlayerSpecificAlgebraicCoinCost.polynomialCoefficient*(p.1+p.2.1+3)^3) :=
  mul (c PlayerSpecificAlgebraicCoinCost.polynomialCoefficient)
    (pow (add (add PlayerSpecificPolynomialTripleTerms.first
      PlayerSpecificPolynomialTripleTerms.second) (c 3)) 3)

theorem work : E (fun p =>
    PlayerSpecificFourSmallDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add (add (add (add
    slice_bits slice_bits) coin_work) slice_remaining)
    PlayerSpecificFourMergedDrawEnvelope.work)
    PlayerSpecificFourReflectedDrawEnvelope.work) (c 2)
  simpa only [PlayerSpecificFourSmallDrawSourceCost.work] using hall

end Blotto.PlayerSpecificFourSmallDrawEnvelope
