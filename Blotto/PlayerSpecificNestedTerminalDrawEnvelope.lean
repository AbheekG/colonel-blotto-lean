import Blotto.PlayerSpecificNestedSpecDrawEnvelope
import Blotto.PlayerSpecificNestedEndpointEnvelopes
import Blotto.PlayerSpecificNestedTerminalDrawSourceCost

/-! The reached nested terminal draw, including endpoint preparation,
closed-probability draw and final restoration, has polynomial source work. -/
namespace Blotto.PlayerSpecificNestedTerminalDrawEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem preparation : E (fun p =>
    PlayerSpecificNestedTerminalPreparationSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    PlayerSpecificNestedEndpointEnvelopes.terminal_preparation_work
    PlayerSpecificPolynomialTripleTerms.first

private theorem stepped_size : E (fun p => step p.1+p.2.1+p.2.2) := by
  have hs := PlayerSpecificSourcePolynomialAutomation.step_envelope
    PlayerSpecificPolynomialTripleTerms.first
  exact add (add hs PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third

private theorem draw : E (fun p =>
    PlayerSpecificNestedSpecDrawSourceCost.work (step p.1) p.2.1 p.2.2) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := S)
    (f := fun q : ℕ × ℕ × ℕ =>
      PlayerSpecificNestedSpecDrawSourceCost.work q.1 q.2.1 q.2.2)
    (g := fun p : ℕ × ℕ × ℕ => (step p.1,p.2.1,p.2.2))
    PlayerSpecificNestedSpecDrawEnvelope.work stepped_size

private theorem output_height : E (fun p =>
    PlayerSpecificNestedTerminalDrawSourceCost.outputHeight p.1 p.2.2) :=
  PlayerSpecificPolynomialTripleTerms.lift_first_third
    PlayerSpecificNestedProfileHeightsEnvelope.terminal_output_height

private theorem restore : E (fun p =>
    PlayerSpecificNestedRestoreSourceCost.work
      (PlayerSpecificNestedTerminalDrawSourceCost.outputHeight p.1 p.2.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ =>
      PlayerSpecificNestedTerminalDrawSourceCost.outputHeight p.1 p.2.2)
    PlayerSpecificNestedEndpointEnvelopes.restore_work output_height

theorem work : E (fun p =>
    PlayerSpecificNestedTerminalDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add preparation draw) restore) (c 2)
  simpa only [PlayerSpecificNestedTerminalDrawSourceCost.work] using hall

end Blotto.PlayerSpecificNestedTerminalDrawEnvelope
