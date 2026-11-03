import Blotto.PlayerSpecificFiniteDrawMeasuredEnvelope
import Blotto.PlayerSpecificInitialMinimumCost

/-! The measured parameter description and positive-minimum search have
polynomial work in the original rational input length. -/
namespace Blotto.PlayerSpecificInitialMinimumEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev E (f : ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p*g p) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ × ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun p => f p^k) := NaturalPolynomialEnvelope.pow hf k
private theorem n1 : E (fun p => p.1+1) := add PlayerSpecificPolynomialPairTerms.first (c 1)
private theorem l1 : E (fun p => p.2+1) := add PlayerSpecificPolynomialPairTerms.second (c 1)
private theorem size : E (fun p => PlayerSpecificAlgebraicInitialVectorBudget.size p.1 p.2) := by
  simpa only [PlayerSpecificAlgebraicInitialVectorBudget.size] using mul n1 l1

private theorem description_preparation : E (fun p =>
    PlayerSpecificFiniteParameterDescriptionCost.preparationBound p.1 p.2) := by
  have hw := mul (c PlayerSpecificFiniteParameterBudget.widthCoefficient) size
  have hwork := mul (pow n1 3) l1
  have h := mul (mul
    (c (PlayerSpecificFiniteParameterBudget.workCoefficient*
      (PlayerSpecificFiniteParameterBudget.widthCoefficient*
        PlayerSpecificFiniteParameterBudget.widthCoefficient+
        PlayerSpecificFiniteParameterBudget.widthCoefficient))) hwork) (pow size 2)
  simpa only [PlayerSpecificFiniteParameterDescriptionCost.preparationBound,
    PlayerSpecificFiniteParameterBudget.work,
    PlayerSpecificFiniteParameterBudget.size,
    PlayerSpecificAlgebraicInitialVectorBudget.size] using h

private theorem minimum_size : E (fun p => PlayerSpecificMinimumPolynomialCost.size p.1 p.2) := by
  simpa only [PlayerSpecificMinimumPolynomialCost.size] using mul n1 l1

theorem work : E (fun p => PlayerSpecificInitialMinimumCost.totalBound p.1 p.2) := by
  have hvector := mul (mul
    (c PlayerSpecificAlgebraicInitialVectorCost.polynomialCoefficient) n1) (pow size 3)
  have hlengths := mul (mul
    (c PlayerSpecificInitialLengthListCost.polynomialCoefficient) n1) (pow size 2)
  have hminimum := mul (mul
    (c PlayerSpecificMinimumPolynomialCost.polynomialCoefficient) n1) (pow minimum_size 4)
  have hparent := mul (mul
    (c PlayerSpecificInitialMinimumParentCost.polynomialCoefficient) n1) (pow size 2)
  have haccepted := add (add (add hvector hlengths) hminimum) hparent
  have hdescription := add description_preparation
    (mul (c 1000) (pow (add description_preparation (c 2)) 3))
  have hall := add (add hdescription haccepted) (c 4)
  simpa only [PlayerSpecificInitialMinimumCost.totalBound,
    PlayerSpecificInitialMinimumCost.descriptionBound,
    PlayerSpecificInitialMinimumCost.acceptedBound,
    PlayerSpecificInitialMinimumCost.vectorBound,
    PlayerSpecificInitialMinimumCost.lengthsBound,
    PlayerSpecificInitialMinimumCost.minimumBound,
    PlayerSpecificInitialMinimumCost.parentBound] using hall

end Blotto.PlayerSpecificInitialMinimumEnvelope
