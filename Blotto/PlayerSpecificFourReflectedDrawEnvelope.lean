import Blotto.PlayerSpecificFourReflectedPathEnvelope
import Blotto.PlayerSpecificNestedTerminalDrawEnvelope
import Blotto.PlayerSpecificFourReflectedDrawSourceCost

/-! The complete reflected four-variable draw source expression is
polynomial in original row height and both fair-bit precisions. -/
namespace Blotto.PlayerSpecificFourReflectedDrawEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
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

private theorem packet_size : E (fun p =>
    PlayerSpecificFourReflectedDrawSourceCost.packetSize p.2.1 p.2.2) := by
  have h2 := mul (c 2) PlayerSpecificPolynomialTripleTerms.second
  have h17 := mul (c 17) PlayerSpecificPolynomialTripleTerms.second
  have hall := add h2 (add (add h17 PlayerSpecificPolynomialTripleTerms.third)
    PlayerSpecificPolynomialTripleTerms.third)
  simpa only [PlayerSpecificFourReflectedDrawSourceCost.packetSize] using hall

private theorem bit_work : E (fun p =>
    PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificFourReflectedDrawSourceCost.packetSize p.2.1 p.2.2+1)^3) :=
  mul (c PlayerSpecificBitSlicePolynomial.coefficient)
    (pow (add packet_size (c 1)) 3)

private theorem path_work : E (fun p =>
    PlayerSpecificFourReflectedPathSourceCost.work p.1 p.2.1) :=
  PlayerSpecificPolynomialTripleTerms.lift_first_second
    PlayerSpecificFourReflectedPathEnvelope.work

private theorem terminal_input : E (fun p =>
    PlayerSpecificFourReflectedTerminalSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun T : ℕ => T)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    PlayerSpecificFourInputEnvelopes.reflected_terminal
    PlayerSpecificPolynomialTripleTerms.first

private theorem iterated_size : E (fun p => iterate 16 p.1+p.2.1+p.2.2) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTripleTerms.first 16
  exact add (add hi PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third

private theorem nested_draw : E (fun p =>
    PlayerSpecificNestedTerminalDrawSourceCost.work (iterate 16 p.1) p.2.1 p.2.2) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := S)
    (f := fun q : ℕ × ℕ × ℕ =>
      PlayerSpecificNestedTerminalDrawSourceCost.work q.1 q.2.1 q.2.2)
    (g := fun p : ℕ × ℕ × ℕ => (iterate 16 p.1,p.2.1,p.2.2))
    PlayerSpecificNestedTerminalDrawEnvelope.work iterated_size

private theorem output_height : E (fun p =>
    PlayerSpecificFourReflectedDrawSourceCost.outputHeight p.1 p.2.2) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTripleTerms.first 16
  have hsize := add hi PlayerSpecificPolynomialTripleTerms.third
  have h := PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := PlayerSpecificPolynomialPairTerms.size)
    (f := fun q : ℕ × ℕ => PlayerSpecificNestedTerminalDrawSourceCost.outputHeight q.1 q.2)
    (g := fun p : ℕ × ℕ × ℕ => (iterate 16 p.1,p.2.2))
    PlayerSpecificNestedProfileHeightsEnvelope.terminal_output_height hsize
  simpa only [PlayerSpecificFourReflectedDrawSourceCost.outputHeight] using h

private theorem append_work : E (fun p =>
    PlayerSpecificReflectAppendSourceCost.work
      (PlayerSpecificFourReflectedDrawSourceCost.outputHeight p.1 p.2.2)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ =>
      PlayerSpecificFourReflectedDrawSourceCost.outputHeight p.1 p.2.2)
    PlayerSpecificFourInputEnvelopes.reflect_append output_height

theorem work : E (fun p =>
    PlayerSpecificFourReflectedDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add (add (add (add bit_work bit_work)
    path_work) terminal_input) nested_draw) append_work) (c 2)
  simpa only [PlayerSpecificFourReflectedDrawSourceCost.work] using hall

end Blotto.PlayerSpecificFourReflectedDrawEnvelope
