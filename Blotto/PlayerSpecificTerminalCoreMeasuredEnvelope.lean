import Blotto.PlayerSpecificPolynomialQuadrupleTerms
import Blotto.PlayerSpecificTerminalCoreMeasuredSourceCost

/-! The reached-state terminal core has polynomial source work in all four inputs. -/
namespace Blotto.PlayerSpecificTerminalCoreMeasuredEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialQuadrupleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem reached_draw : E (fun p =>
    PlayerSpecificTerminalCoreDrawSourceCost.work
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2.1)
      p.2.2.1 p.2.2.2) := by
  have hp := PlayerSpecificPolynomialQuadrupleTerms.lift_first_second
    PlayerSpecificTerminalCoreInputEnvelope.preparation_height
  have hs := add (add hp PlayerSpecificPolynomialQuadrupleTerms.third)
    PlayerSpecificPolynomialQuadrupleTerms.fourth
  exact PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := PlayerSpecificPolynomialTripleTerms.size)
    (g := fun p : ℕ × ℕ × ℕ × ℕ =>
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2.1,
        p.2.2.1,p.2.2.2))
    PlayerSpecificTerminalCoreDrawEnvelope.work hs

theorem work : E (fun p =>
    PlayerSpecificTerminalCoreMeasuredSourceCost.work p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hi := PlayerSpecificPolynomialQuadrupleTerms.lift_first_second
    PlayerSpecificTerminalCoreInputEnvelope.work
  have hall := add (add hi reached_draw) (c 2)
  change E (fun p => PlayerSpecificTerminalCoreInputSourceCost.work p.1 p.2.1+
    PlayerSpecificTerminalCoreDrawSourceCost.work
      (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height p.1 p.2.1)
      p.2.2.1 p.2.2.2+2)
  exact hall

end Blotto.PlayerSpecificTerminalCoreMeasuredEnvelope
