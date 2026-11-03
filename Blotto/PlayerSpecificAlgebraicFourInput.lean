import Blotto.PlayerSpecificAlgebraicNestedSpecDraw
import Blotto.RealFourParametersCode

/-! Raw retained-field four-variable inputs and their cached scalar
programs. All parameters are computed from the six original rows. -/
namespace Blotto.PlayerSpecificAlgebraicFourInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Input where
  budget : Data
  first : Data
  second : Data
  third : Data
  length : Data
  probability : Data

def environment (a : Input) : FixedArrayTable 6 Data :=
  FixedArrayTable.ofFn ![a.budget,a.first,a.second,a.third,a.length,a.probability]

def parameters (model : RationalCostModel) (root : Candidate) (a : Input) : FixedArrayTable 8 Data :=
  let env := environment a
  FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (RationalFourParametersCode.programs j))

structure Values (a : Input) (i : FourInput) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.B
  first : realEvaluate a.first x=i.u
  second : realEvaluate a.second x=i.v
  third : realEvaluate a.third x=i.w
  length : realEvaluate a.length x=i.ell
  probability : realEvaluate a.probability x=i.p

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  first : Reduced root.polynomial a.first ∧ HasHeight a.first T
  second : Reduced root.polynomial a.second ∧ HasHeight a.second T
  third : Reduced root.polynomial a.third ∧ HasHeight a.third T
  length : Reduced root.polynomial a.length ∧ HasHeight a.length T
  probability : Reduced root.polynomial a.probability ∧ HasHeight a.probability T

theorem environment_value (a : Input) (i : FourInput) (x : ℝ) (ha : Values a i x) :
    PlayerSpecificAlgebraicExpression.realEnv (environment a) x=RealFourParametersCode.environment i := by
  unfold PlayerSpecificAlgebraicExpression.realEnv RealFourParametersCode.environment
  congr 1
  funext j
  fin_cases j <;> simp [environment,FixedArrayTable.read_ofFn,
    ha.budget,ha.first,ha.second,ha.third,ha.length,ha.probability]

theorem environment_bounds (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T) :
    ∀ j,Reduced root.polynomial ((environment a).read j) ∧ HasHeight ((environment a).read j) T := by
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact ha.budget
  · exact ha.first
  · exact ha.second
  · exact ha.third
  · exact ha.length
  · exact ha.probability

theorem parameter_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x)
    (T : ℕ) (hfit : Fits root a T) (j : Fin 8) :
    realEvaluate ((parameters model root a).read j) x=RealFourParametersCode.values i j := by
  rw [parameters,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx
      (fun k => (environment_bounds root a T hfit k).1),environment_value a i x ha]
  exact RealFourParametersCode.value_eq i j

theorem parameter_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    ∀ j,Reduced root.polynomial ((parameters model root a).read j) ∧
      HasHeight ((parameters model root a).read j) (iterate 13 T) := by
  have he := environment_bounds root a T ha
  intro j
  rw [parameters,FixedArrayTable.read_ofFn]
  refine ⟨PlayerSpecificAlgebraicExpression.reduced model root _ _ hm hm0 (fun k => (he k).1),?_⟩
  have hh := PlayerSpecificAlgebraicExpressionHeights.run_height model root (environment a)
    (RationalFourParametersCode.programs j) hm hm0 hml T hmT (by omega) he
    ((RationalFourParametersCode.programs j).LiteralHeights_mono hT (RationalFourParametersCode.literals j))
  exact mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono T (RationalFourParametersCode.depth j))

end Blotto.PlayerSpecificAlgebraicFourInput
