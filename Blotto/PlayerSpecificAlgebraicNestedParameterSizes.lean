import Blotto.PlayerSpecificAlgebraicDescriptorShift

/-! The actual scalar and first-geometry parameter programs have fixed
height bounds in the six raw input rows and the supplied algebraic scalar. -/
namespace Blotto.PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  first : Reduced root.polynomial a.first ∧ HasHeight a.first T
  second : Reduced root.polynomial a.second ∧ HasHeight a.second T
  long : Reduced root.polynomial a.long ∧ HasHeight a.long T
  short : Reduced root.polynomial a.short ∧ HasHeight a.short T
  probability : Reduced root.polynomial a.probability ∧ HasHeight a.probability T

theorem environment_bounds (root : Candidate) (a : Input) (extra : Data) (T : ℕ) (hfit : Fits root a T)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra T) :
    ∀ j,Reduced root.polynomial ((environment a extra).read j) ∧ HasHeight ((environment a extra).read j) T := by
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact hfit.budget
  · exact hfit.first
  · exact hfit.second
  · exact hfit.long
  · exact hfit.short
  · exact hfit.probability
  · exact hExtra

theorem scalar_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (T : ℕ)
    (hfit : Fits root a T) (hExtra : Reduced root.polynomial extra ∧ HasHeight extra T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (j : Fin 6) :
    Reduced root.polynomial (scalar model root a extra j) ∧ HasHeight (scalar model root a extra j) (iterate 9 T) := by
  have he:=environment_bounds root a extra T hfit hExtra
  refine ⟨PlayerSpecificAlgebraicExpression.reduced model root _ _ hm hm0 (fun j => (he j).1),?_⟩
  have hh:=PlayerSpecificAlgebraicExpressionHeights.run_height model root (environment a extra)
    (RationalNestedParametersCode.scalarPrograms j) hm hm0 hml T hmT (by omega) he
    ((RationalNestedParametersCode.scalarPrograms j).LiteralHeights_mono hT (RationalNestedParametersCode.scalar_literals j))
  exact mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono T (RationalNestedParametersCode.scalar_depth j))

theorem first_environment_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (T : ℕ)
    (hfit : Fits root a T) (hExtra : Reduced root.polynomial extra ∧ HasHeight extra T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    ∀ j,Reduced root.polynomial ((firstEnvironment model root a extra).read j) ∧
      HasHeight ((firstEnvironment model root a extra).read j) (iterate 4 T) := by
  have he:=environment_bounds root a extra T hfit hExtra
  intro j
  rw [firstEnvironment,FixedArrayTable.read_ofFn]
  refine ⟨PlayerSpecificAlgebraicExpression.reduced model root _ _ hm hm0 (fun j => (he j).1),?_⟩
  have hh:=PlayerSpecificAlgebraicExpressionHeights.run_height model root (environment a extra)
    (RationalNestedParametersCode.firstParameters j) hm hm0 hml T hmT (by omega) he
    ((RationalNestedParametersCode.firstParameters j).LiteralHeights_mono hT (RationalNestedParametersCode.first_parameter_literals j))
  exact mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono T (RationalNestedParametersCode.first_parameter_depth j))

end Blotto.PlayerSpecificAlgebraicNestedParameterSizes
