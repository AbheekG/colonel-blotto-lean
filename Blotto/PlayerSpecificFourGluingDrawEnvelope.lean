import Blotto.PlayerSpecificOverlapNineEnvelope
import Blotto.PlayerSpecificPolynomialTripleTerms
import Blotto.PlayerSpecificFourGluingDrawSourceCost

/-! The normal four-variable gluing branch, including both parent
descriptors and the cached overlap table, has polynomial source work. -/
namespace Blotto.PlayerSpecificFourGluingDrawEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private theorem source_work : NaturalPolynomialEnvelope (fun H : ℕ => H)
    (fun H => PlayerSpecificFourGluingSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 25 3
    PlayerSpecificFourParameterSourceCost.coefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 13 30 3
    PlayerSpecificFourParentInputSourceCost.coefficient
  have h3 := PlayerSpecificPolynomialTerms.iterated 13 1 3
    PlayerSpecificUnorderedThreeSourceCost.coefficient
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTerms.input 33
  have h4 := PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := fun H : ℕ => H) (sizeB := fun H : ℕ => H)
    (g := fun H => iterate 33 H)
    PlayerSpecificOverlapNineEnvelope.overlap_table hi
  have hall := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add
      (NaturalPolynomialEnvelope.add
        (NaturalPolynomialEnvelope.add
          (NaturalPolynomialEnvelope.add
            (NaturalPolynomialEnvelope.add h1 h2) h3) h2) h3) h4)
      (PlayerSpecificPolynomialTerms.constant 8)
  simpa only [PlayerSpecificFourGluingSourceCost.work,iterate] using hall

private abbrev S := PlayerSpecificPolynomialTripleTerms.size
private abbrev E (f : ℕ × ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg

private theorem input : E (fun p => PlayerSpecificFourGluingSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    source_work PlayerSpecificPolynomialTripleTerms.first

private theorem frame_height : E (fun p => iterate 43 p.1+4+81+p.2.1+p.2.2+1) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTripleTerms.first 43
  exact add (add (add (add (add hi (c 4)) (c 81))
    PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third) (c 1)

private theorem segment : E (fun p =>
    PlayerSpecificSegmentDrawSourceCost.coefficient*
      (iterate 43 p.1+4+81+p.2.1+p.2.2+1)^16) :=
  NaturalPolynomialEnvelope.mul
    (c PlayerSpecificSegmentDrawSourceCost.coefficient)
    (NaturalPolynomialEnvelope.pow frame_height 16)

theorem work : E (fun p => PlayerSpecificFourGluingDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add input segment) (c 2)
  simpa only [PlayerSpecificFourGluingDrawSourceCost.work] using hall

end Blotto.PlayerSpecificFourGluingDrawEnvelope
