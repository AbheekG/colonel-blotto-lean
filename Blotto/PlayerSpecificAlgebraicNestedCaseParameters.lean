import Blotto.PlayerSpecificAlgebraicResidualReference

/-! Actual cached case parameters share one seven-entry expression
environment. Scalar formulas and comparison values are computed from the
raw nested rows, never supplied as decision or arithmetic oracles. -/
namespace Blotto.PlayerSpecificAlgebraicNestedCaseParameters
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared where
  u : Data
  v : Data
  h : Data
  mirror : Data
  secondAlpha : Data
  thirdAlpha : Data

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared :=
  let geometry:=PlayerSpecificAlgebraicResidualEnvironment.environment root a
  let env:=PlayerSpecificAlgebraicNestedInput.environment a []
  ⟨geometry.read 0,geometry.read 1,geometry.read 3,
    PlayerSpecificAlgebraicExpression.run model root env (RationalNestedParametersCode.scalarPrograms 3),
    PlayerSpecificAlgebraicExpression.run model root env (RationalNestedParametersCode.scalarPrograms 4),
    PlayerSpecificAlgebraicExpression.run model root env (RationalNestedParametersCode.scalarPrograms 5)⟩

structure Values (p : Prepared) (i : NestedInput) (x : ℝ) : Prop where
  u : realEvaluate p.u x=i.u
  v : realEvaluate p.v x=i.v
  h : realEvaluate p.h x=i.h
  mirror : realEvaluate p.mirror x=i.mirrorLength
  secondAlpha : realEvaluate p.secondAlpha x=i.secondAlpha
  thirdAlpha : realEvaluate p.thirdAlpha x=i.thirdAlpha

theorem values (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T) :
    Values (prepare model root a) i x := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have henv:=PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a [] T hfit (nil_reduced _ hm0)
  have hs3:=scalar_value model root a i hm hirr hv x hx ha [] henv 3
  have hs4:=scalar_value model root a i hm hirr hv x hx ha [] henv 4
  have hs5:=scalar_value model root a i hm hirr hv x hx ha [] henv 5
  constructor
  · simp [prepare,PlayerSpecificAlgebraicResidualEnvironment.environment,FixedArrayTable.read_ofFn,
      PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1,ha.budget,ha.first,NestedInput.u]
  · simp [prepare,PlayerSpecificAlgebraicResidualEnvironment.environment,FixedArrayTable.read_ofFn,
      PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1,ha.budget,ha.second,NestedInput.v]
  · simp [prepare,PlayerSpecificAlgebraicResidualEnvironment.environment,FixedArrayTable.read_ofFn,
      PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,
      ha.long,ha.short,ha.probability,NestedInput.h]
  · simpa [prepare,scalar,RealNestedParametersCode.scalarValues] using hs3
  · simpa [prepare,scalar,RealNestedParametersCode.scalarValues] using hs4
  · simpa [prepare,scalar,RealNestedParametersCode.scalarValues] using hs5

structure Bounds (root : Candidate) (p : Prepared) (T : ℕ) : Prop where
  u : Reduced root.polynomial p.u ∧ HasHeight p.u T
  v : Reduced root.polynomial p.v ∧ HasHeight p.v T
  h : Reduced root.polynomial p.h ∧ HasHeight p.h T
  mirror : Reduced root.polynomial p.mirror ∧ HasHeight p.mirror T
  secondAlpha : Reduced root.polynomial p.secondAlpha ∧ HasHeight p.secondAlpha T
  thirdAlpha : Reduced root.polynomial p.thirdAlpha ∧ HasHeight p.thirdAlpha T

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) : Bounds root (prepare model root a) (iterate 9 T) := by
  have hg:=PlayerSpecificAlgebraicResidualEnvironment.bounds root a T hfit hm hm0 hml hmT
  have h29:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (show 2≤9 by omega)
  have hs:=fun j => scalar_bounds model root a [] T hfit ⟨nil_reduced _ hm0,nil_height _⟩ hm hm0 hml hmT hT j
  refine ⟨?_,?_,?_,hs 3,hs 4,hs 5⟩
  · exact ⟨(hg 0).1,mono (hg 0).2 h29⟩
  · exact ⟨(hg 1).1,mono (hg 1).2 h29⟩
  · exact ⟨(hg 3).1,mono (hg 3).2 h29⟩

end Blotto.PlayerSpecificAlgebraicNestedCaseParameters
