import Blotto.PlayerSpecificMixtureScalarExecution

/-! Complete scalar mixture work and derived cached-complement sizes. -/
namespace Blotto.PlayerSpecificMixtureScalarSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificMixtureScalarExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

def complementCoefficient : ℕ := 6*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 1+2
def scaleCoefficient : ℕ := 7*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 1+2
theorem profile (C X : ℕ) (hX : 1≤X) : C*X+2≤(C+2)*X := by nlinarith only [hX]

theorem complement_cost (root : Candidate) (p : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (hp : Reduced root.polynomial p ∧ HasHeight p H) :
    (complement RationalCostModel.schoolbook root p).2≤complementCoefficient*(H+13)^3 := by
  have henv : ∀ j,Reduced root.polynomial ((oneEnvironment p).read j) ∧ HasHeight ((oneEnvironment p).read j) H := by
    intro j; simpa only [oneEnvironment,FixedArrayTable.read_ofFn] using hp
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (oneEnvironment p) complementPrograms H 1 hm hm0 hml hmH he hv henv
    complement_depth (fun j => complement_literals j H hH)
  rw [complement_operations,show H+1+1+11=H+13 by omega] at hc
  change _+price RationalCostModel.schoolbook [.control 0]≤_
  rw [packing]
  exact (Nat.add_le_add_right hc 2).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+13) 3)))

theorem scale_cost (root : Candidate) (p q : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hp : Reduced root.polynomial p ∧ HasHeight p H) (hq : Reduced root.polynomial q ∧ HasHeight q H) :
    (scale RationalCostModel.schoolbook root p q).2≤scaleCoefficient*(H+14)^3 := by
  have henv : ∀ j,Reduced root.polynomial ((twoEnvironment p q).read j) ∧ HasHeight ((twoEnvironment p q).read j) H := by
    intro j
    fin_cases j
    · simpa [twoEnvironment,FixedArrayTable.read_ofFn] using hp
    · simpa [twoEnvironment,FixedArrayTable.read_ofFn] using hq
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (twoEnvironment p q) scalePrograms H 1 hm hm0 hml hmH he hv henv
    scale_depth (fun j => scale_literals j H)
  rw [scale_operations,show H+1+2+11=H+14 by omega] at hc
  change _+price RationalCostModel.schoolbook [.control 0]≤_
  rw [packing]
  exact (Nat.add_le_add_right hc 2).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+14) 3)))

theorem complement_bounds (model : RationalCostModel) (root : Candidate) (p : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 1≤H) (hp : Reduced root.polynomial p ∧ HasHeight p H) :
    Reduced root.polynomial (complement model root p).1 ∧
      HasHeight (complement model root p).1 (PlayerSpecificAlgebraicHeightEnvelope.iterate 2 H) := by
  let env:=oneEnvironment p
  let e:RationalExpression 1:=.sub (.literal 1) (.input 0)
  have henv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H := by
    intro j; simpa only [env,oneEnvironment,FixedArrayTable.read_ofFn] using hp
  have hl : e.LiteralHeights H := ⟨one_height.mono hH,trivial⟩
  have hr:=PlayerSpecificAlgebraicExpression.reduced model root env e hm hm0 (fun j => (henv j).1)
  have hh:=PlayerSpecificAlgebraicExpressionHeights.run_height model root env e hm hm0 hml H hmH hH henv hl
  simpa only [complement,PlayerSpecificExpressionVectorExecution.read_value,complementPrograms,FixedArrayTable.read_ofFn,
    env,e,PlayerSpecificAlgebraicExpressionBudget.height,RationalExpression.depth,Nat.max_self] using And.intro hr hh

end Blotto.PlayerSpecificMixtureScalarSourceCost
