import Blotto.PlayerSpecificFourInputEnvelopes
import Blotto.PlayerSpecificPolynomialTripleTerms
import Blotto.PlayerSpecificSplitFirstTwoSourceCost
import Blotto.PlayerSpecificFourMergedDrawSourceCost

/-! The small uniform merged four-variable draw, including its two-way
split and three-variable segment draw, has polynomial source work. -/
namespace Blotto.PlayerSpecificFourMergedDrawEnvelope
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

theorem split_first_two : NaturalPolynomialEnvelope (fun H : ℕ => H)
    (fun H => PlayerSpecificSplitFirstTwoSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h2 := PlayerSpecificPolynomialTerms.stepped 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h3 := PlayerSpecificPolynomialTerms.iterated 2 14 3
    PlayerSpecificMixtureScalarSourceCost.scaleCoefficient
  have h4 := PlayerSpecificPolynomialTerms.iterated 3 11 3
    (2000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add
      (NaturalPolynomialEnvelope.add
        (NaturalPolynomialEnvelope.add
          (NaturalPolynomialEnvelope.add
            (NaturalPolynomialEnvelope.add h1 h2) h2) h3) h3) h4)
      (PlayerSpecificPolynomialTerms.constant 14)
  simpa only [PlayerSpecificSplitFirstTwoSourceCost.work,iterate] using hall

private theorem merged_input : E (fun p => PlayerSpecificFourMergedInputSourceCost.work p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ => p.1)
    PlayerSpecificFourInputEnvelopes.merged_input
    PlayerSpecificPolynomialTripleTerms.first

private theorem frame_height : E (fun p => iterate 15 p.1+p.2.1+p.2.2+1) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTripleTerms.first 15
  exact add (add (add hi PlayerSpecificPolynomialTripleTerms.second)
    PlayerSpecificPolynomialTripleTerms.third) (c 1)

private theorem segment_work : E (fun p =>
    PlayerSpecificThreeDrawSourceCost.coefficient*(iterate 15 p.1+p.2.1+p.2.2+1)^16) :=
  mul (c PlayerSpecificThreeDrawSourceCost.coefficient) (pow frame_height 16)

private theorem split_height : E (fun p =>
    iterate 3 (iterate 35 p.1+2*p.2.2+6)) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTripleTerms.first 35
  have hk := mul (c 2) PlayerSpecificPolynomialTripleTerms.third
  have hbase := add (add hi hk) (c 6)
  exact PlayerSpecificSourcePolynomialAutomation.iterate_envelope hbase 3

private theorem split_work : E (fun p =>
    PlayerSpecificSplitFirstTwoSourceCost.work
      (iterate 3 (iterate 35 p.1+2*p.2.2+6))) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := S) (sizeB := fun H : ℕ => H)
    (g := fun p : ℕ × ℕ × ℕ => iterate 3 (iterate 35 p.1+2*p.2.2+6))
    split_first_two split_height

theorem work : E (fun p => PlayerSpecificFourMergedDrawSourceCost.work p.1 p.2.1 p.2.2) := by
  have hall := add (add (add merged_input segment_work) split_work) (c 2)
  simpa only [PlayerSpecificFourMergedDrawSourceCost.work] using hall

end Blotto.PlayerSpecificFourMergedDrawEnvelope
