import Blotto.PlayerSpecificFiniteInputHeightEnvelope
import Blotto.PlayerSpecificFiniteDrawMeasuredSourceCost

/-! Original rational finite draw source work is polynomial in public input size and precisions. -/
namespace Blotto.PlayerSpecificFiniteDrawMeasuredEnvelope
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

private theorem packet_bits : E (fun p =>
    PlayerSpecificAlgebraicFiniteDraw.bitCount p.1 p.2.2.1 p.2.2.2) := by
  have hsub := NaturalPolynomialEnvelope.sub
    (g := fun _ : ℕ × ℕ × ℕ × ℕ => 1)
    PlayerSpecificPolynomialQuadrupleTerms.first
  have hcore := add (add
    (add (mul (c 80) PlayerSpecificPolynomialQuadrupleTerms.third)
      PlayerSpecificPolynomialQuadrupleTerms.fourth)
    PlayerSpecificPolynomialQuadrupleTerms.fourth) (c 0)
  have h := add (mul hsub PlayerSpecificPolynomialQuadrupleTerms.third) hcore
  simpa only [PlayerSpecificAlgebraicFiniteDraw.bitCount,
    PlayerSpecificAlgebraicTerminalCoreDraw.bitCount,Nat.add_zero] using h

private theorem entry_height : E (fun p =>
    PlayerSpecificResourceEntryInput.height p.1 p.2.1) :=
  PlayerSpecificPolynomialQuadrupleTerms.lift_first_second
    PlayerSpecificFiniteInputHeightEnvelope.resource_entry

private theorem leaf : E (fun p =>
    PlayerSpecificTerminalLeafMeasuredSourceCost.work p.1
      (PlayerSpecificResourceEntryInput.height p.1 p.2.1) p.2.2.1 p.2.2.2) := by
  have hs := add (add (add PlayerSpecificPolynomialQuadrupleTerms.first entry_height)
    PlayerSpecificPolynomialQuadrupleTerms.third) PlayerSpecificPolynomialQuadrupleTerms.fourth
  exact PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := S)
    (g := fun p : ℕ × ℕ × ℕ × ℕ =>
      (p.1,PlayerSpecificResourceEntryInput.height p.1 p.2.1,p.2.2.1,p.2.2.2))
    PlayerSpecificTerminalLeafMeasuredEnvelope.work hs

theorem work : E (fun p =>
    2*PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicFiniteDraw.bitCount p.1 p.2.2.1 p.2.2.2+1)^3+
    PlayerSpecificResourceEntryPriceProfile.coefficient*(p.1+1)^7*(p.2.1+p.2.2.1+1)^3+
    PlayerSpecificTerminalLeafMeasuredSourceCost.work p.1
      (PlayerSpecificResourceEntryInput.height p.1 p.2.1) p.2.2.1 p.2.2.2+2) := by
  have hbits := mul (c (2*PlayerSpecificBitSlicePolynomial.coefficient))
    (pow (add packet_bits (c 1)) 3)
  have hentry := mul
    (mul (c PlayerSpecificResourceEntryPriceProfile.coefficient)
      (pow (add PlayerSpecificPolynomialQuadrupleTerms.first (c 1)) 7))
    (pow (add (add PlayerSpecificPolynomialQuadrupleTerms.second
      PlayerSpecificPolynomialQuadrupleTerms.third) (c 1)) 3)
  exact add (add (add hbits hentry) leaf) (c 2)

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) :
    ∃ C d : ℕ, ∀ H K,
      PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K ≤
      C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+H+K+1)^d := by
  obtain ⟨C,d,h⟩ := work
  refine ⟨C,d,?_⟩
  intro H K
  exact h (N,PlayerSpecificInitialPositivePrecision.inputSize i,H,K)

end Blotto.PlayerSpecificFiniteDrawMeasuredEnvelope
