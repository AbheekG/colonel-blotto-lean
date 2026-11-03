import Blotto.PlayerSpecificInitialMinimumParentCost

/-! Complete original-input preparation through initial algebraic
arrays and positive minimum precision. Bounds are explicit sums of fixed
polynomials; all executing callers and exact rejection are included. -/
namespace Blotto.PlayerSpecificInitialMinimumCost
open PlayerSpecificAlgebraicInitialVectorBudget PlayerSpecificInitialMinimumValues PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def vectorBound (N L : ℕ) : ℕ := PlayerSpecificAlgebraicInitialVectorCost.polynomialCoefficient*(N+1)*size N L^3
def lengthsBound (N L : ℕ) : ℕ := PlayerSpecificInitialLengthListCost.polynomialCoefficient*(N+1)*size N L^2
def minimumBound (N L : ℕ) : ℕ := PlayerSpecificMinimumPolynomialCost.polynomialCoefficient*(N+1)*PlayerSpecificMinimumPolynomialCost.size N L^4
def parentBound (N L : ℕ) : ℕ := PlayerSpecificInitialMinimumParentCost.polynomialCoefficient*(N+1)*size N L^2
def acceptedBound (N L : ℕ) : ℕ := vectorBound N L+lengthsBound N L+minimumBound N L+parentBound N L
def descriptionBound (N L : ℕ) : ℕ := PlayerSpecificFiniteParameterDescriptionCost.preparationBound N L+
  1000*(PlayerSpecificFiniteParameterDescriptionCost.preparationBound N L+2)^3
def totalBound (N L : ℕ) : ℕ := descriptionBound N L+acceptedBound N L+4

theorem price_eq {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).2=
      (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).2+
      (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook (PlayerSpecificInitialLengthListCost.stored i r)).2+
      (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+(minimum i r).work+
      (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+
      price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N (minimum i r).quantum (minimum i r).exponent)+
      32*(N+1)*address N := rfl

theorem minimum_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+(minimum i r).work≤minimumBound N (inputSize i) := by
  have hold : (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+
      (PlayerSpecificMinimumContract.run i r).work≤minimumBound N (inputSize i) := by
    simpa only [minimumBound,PlayerSpecificMinimumOriginalSizes.inputSize,PlayerSpecificInitialPositivePrecision.inputSize,inputSize] using
      PlayerSpecificMinimumPolynomialCost.polynomial_cost i r hr
  have he:=congrArg (fun result : PlayerSpecificMinimumSearch.Result =>
    (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+result.work) (minimum_value i r)
  exact he.symm ▸ hold

theorem accepted_profile (v l g m p f a V L M P : ℕ) (hv : v≤V) (hl : l≤L) (hm : g+m≤M) (hp : p+f+a≤P) :
    v+l+g+m+p+f+a≤V+L+M+P := by omega

theorem accept_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificInitialMinimumExecution.accept i r).2≤acceptedBound N (inputSize i) := by
  have hv : (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).2≤vectorBound N (inputSize i) :=
    PlayerSpecificAlgebraicInitialVectorCost.polynomial_cost i r hr
  have hl : (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook (PlayerSpecificInitialLengthListCost.stored i r)).2≤lengthsBound N (inputSize i) :=
    PlayerSpecificInitialLengthListCost.polynomial_cost i r hr
  have hm:=minimum_cost i r hr
  have hp : (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+
      price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N (minimum i r).quantum (minimum i r).exponent)+32*(N+1)*address N≤parentBound N (inputSize i) :=
    PlayerSpecificInitialMinimumParentCost.polynomial_cost i r hr
  rw [price_eq]
  unfold acceptedBound
  exact accepted_profile _ _ _ _ _ _ _ _ _ _ _ hv hl hm hp

theorem description_cost {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificFiniteParameterDescription.run i).work≤descriptionBound N (inputSize i) :=
  PlayerSpecificFiniteParameterDescriptionCost.total_work i

theorem source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificInitialMinimumExecution.run i).2≤totalBound N (inputSize i) := by
  have hd:=description_cost i
  have hc0 : price RationalCostModel.schoolbook [.control 0]≤4 := by decide
  have hc1 : price RationalCostModel.schoolbook [.control 1]≤4 := by decide
  unfold PlayerSpecificInitialMinimumExecution.run
  dsimp only
  split
  · dsimp only
    unfold totalBound
    omega
  · rename_i r hr
    have ha:=accept_cost i r hr
    dsimp only
    unfold totalBound
    omega

end Blotto.PlayerSpecificInitialMinimumCost
