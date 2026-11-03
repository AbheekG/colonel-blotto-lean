import Blotto.PlayerSpecificFourSpecDrawEnvelope
import Blotto.PlayerSpecificComplementaryDrawSourcePolynomial
import Blotto.PlayerSpecificTerminalCoreSelectedSourceCost

/-! Polynomial work for every selected terminal-core branch. -/
namespace Blotto.PlayerSpecificTerminalCoreSelectedEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev P := PlayerSpecificPolynomialPairTerms.size
private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k

private theorem bits : E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount p.2.1 p.2.2+1)^3) := by
  have hn := add (add (add
    (mul (c 80) PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third)
    PlayerSpecificPolynomialTripleTerms.third) (c 1)
  have h := mul (c PlayerSpecificBitSlicePolynomial.coefficient) (pow hn 3)
  simpa only [PlayerSpecificAlgebraicTerminalCoreDraw.bitCount] using h

private theorem complementary_pair : NaturalPolynomialEnvelope P
    (fun p : ℕ × ℕ => PlayerSpecificComplementaryDrawSourceCost.work p.1 p.2) := by
  let C := PlayerSpecificComplementaryDrawSourcePolynomial.coefficient
  refine ⟨C*5^3,3,?_⟩
  intro p
  have h := PlayerSpecificComplementaryDrawSourcePolynomial.work_bound p.1 p.2
  have hs : p.1+p.2+5≤5*(P p+1) := by
    dsimp [P,PlayerSpecificPolynomialPairTerms.size]
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs 3)
  calc
    PlayerSpecificComplementaryDrawSourceCost.work p.1 p.2 ≤ C*(p.1+p.2+5)^3 := h
    _ ≤ C*(5*(P p+1))^3 := hp
    _ = (C*5^3)*(P p+1)^3 := by ring

private theorem complementary : E (fun p =>
    PlayerSpecificComplementaryDrawSourceCost.work p.1 p.2.2) :=
  PlayerSpecificPolynomialTripleTerms.lift_first_third complementary_pair

private theorem three : E (fun p =>
    PlayerSpecificThreeDrawSourceCost.coefficient*(p.1+p.2.1+p.2.2+1)^16) :=
  mul (c PlayerSpecificThreeDrawSourceCost.coefficient)
    (pow (add (add (add PlayerSpecificPolynomialTripleTerms.first
      PlayerSpecificPolynomialTripleTerms.second)
      PlayerSpecificPolynomialTripleTerms.third) (c 1)) 16)

private theorem three_step : E (fun p =>
    PlayerSpecificThreeDrawSourceCost.coefficient*(step p.1+p.2.1+p.2.2+1)^16) := by
  have hs := PlayerSpecificSourcePolynomialAutomation.step_envelope
    PlayerSpecificPolynomialTripleTerms.first
  exact mul (c PlayerSpecificThreeDrawSourceCost.coefficient)
    (pow (add (add (add hs PlayerSpecificPolynomialTripleTerms.second)
      PlayerSpecificPolynomialTripleTerms.third) (c 1)) 16)

private theorem final_frame : E (fun p =>
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(p.1+1)^3) :=
  mul (c (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient))
    (pow (add PlayerSpecificPolynomialTripleTerms.first (c 1)) 3)

theorem work : E (fun p =>
    PlayerSpecificTerminalCoreSelectedSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add (add (add (add bits complementary) three)
    three_step) PlayerSpecificFourSpecDrawEnvelope.work) final_frame) (c 2)
  change E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount p.2.1 p.2.2+1)^3+
    PlayerSpecificComplementaryDrawSourceCost.work p.1 p.2.2+
    PlayerSpecificThreeDrawSourceCost.coefficient*(p.1+p.2.1+p.2.2+1)^16+
    PlayerSpecificThreeDrawSourceCost.coefficient*(step p.1+p.2.1+p.2.2+1)^16+
    PlayerSpecificFourSpecDrawSourceCost.work p.1 p.2.1 p.2.2+
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(p.1+1)^3+2)
  exact hall

end Blotto.PlayerSpecificTerminalCoreSelectedEnvelope
