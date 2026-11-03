import Blotto.PlayerSpecificAlgebraicThreeDraw
import Blotto.RealNestedParametersCode

/-! Raw algebraic nested inputs and the actual seven-entry environment
for the retained scalar programs. Real witnesses are proof-only. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Input where
  budget : Data
  first : Data
  second : Data
  long : Data
  short : Data
  probability : Data

structure Values (a : Input) (i : NestedInput) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.M
  first : realEvaluate a.first x=i.a
  second : realEvaluate a.second x=i.d
  long : realEvaluate a.long x=i.c
  short : realEvaluate a.short x=i.t
  probability : realEvaluate a.probability x=i.q

def environment (a : Input) (extra : Data) : FixedArrayTable 7 Data :=
  FixedArrayTable.ofFn ![a.budget,a.first,a.second,a.long,a.short,a.probability,extra]

def scalar (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (j : Fin 6) : Data :=
  PlayerSpecificAlgebraicExpression.run model root (environment a extra) (RationalNestedParametersCode.scalarPrograms j)

def firstEnvironment (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : FixedArrayTable 4 Data :=
  let env:=environment a extra
  FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (RationalNestedParametersCode.firstParameters j))

theorem environment_value (a : Input) (i : NestedInput) (x : ℝ) (ha : Values a i x) (extra : Data) :
    PlayerSpecificAlgebraicExpression.realEnv (environment a extra) x=
      RealNestedParametersCode.environment i (realEvaluate extra x) := by
  unfold PlayerSpecificAlgebraicExpression.realEnv RealNestedParametersCode.environment
  congr 1
  funext j
  fin_cases j <;> simp [environment,FixedArrayTable.read_ofFn,ha.budget,ha.first,ha.second,ha.long,ha.short,ha.probability]

theorem scalar_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x)
    (extra : Data) (hEnv : ∀ j,Reduced root.polynomial ((environment a extra).read j)) (j : Fin 6) :
    realEvaluate (scalar model root a extra j) x=RealNestedParametersCode.scalarValues i (realEvaluate extra x) j := by
  rw [scalar,PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx hEnv,
    environment_value a i x ha extra]
  exact RealNestedParametersCode.scalar_value i _ j

theorem first_environment_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x)
    (extra : Data) (hEnv : ∀ j,Reduced root.polynomial ((environment a extra).read j))
    (htv : i.t≤ i.v) (hs : 0≤realEvaluate extra x ∧ realEvaluate extra x≤ i.t)
    (hp : 0< i.conditionalProbability (realEvaluate extra x)) :
    PlayerSpecificAlgebraicExpression.realEnv (firstEnvironment model root a extra) x=
      RealThreeGeometryCode.environment (i.firstGeometry htv (realEvaluate extra x) hs hp) := by
  unfold PlayerSpecificAlgebraicExpression.realEnv
  have he : RealThreeGeometryCode.environment (i.firstGeometry htv (realEvaluate extra x) hs hp)=
      FixedArrayTable.ofFn (fun j => (RealThreeGeometryCode.environment (i.firstGeometry htv (realEvaluate extra x) hs hp)).read j) := by
    unfold RealThreeGeometryCode.environment
    congr 1
    funext j
    rw [FixedArrayTable.read_ofFn]
  rw [he]
  congr 1
  funext j
  rw [firstEnvironment,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx hEnv,environment_value a i x ha extra]
  exact RealNestedParametersCode.firstParameters_value i htv _ hs hp j

end Blotto.PlayerSpecificAlgebraicNestedInput
