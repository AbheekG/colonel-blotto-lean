import Blotto.PlayerSpecificAlgebraicThreeGeometrySizes

/-! Raw algebraic three-variable inputs and the actual retained-field
geometry transformation. Real input witnesses are proof-only refinements. -/
namespace Blotto.PlayerSpecificAlgebraicThreeInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Input where
  budget : Data
  first : Data
  second : Data
  third : Data
  probability : Data

structure Values (a : Input) (i : ThreeInput) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.B
  first : realEvaluate a.first x=i.a
  second : realEvaluate a.second x=i.d
  third : realEvaluate a.third x=i.c
  probability : realEvaluate a.probability x=i.p

def positive (model : RationalCostModel) (root : Candidate) (a : Input) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le model root
    (PlayerSpecificAlgebraicField.plus root.polynomial a.first a.second) a.budget

def environment (root : Candidate) (a : Input) : FixedArrayTable 4 Data :=
  let u:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.first
  let v:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.second
  let w:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.third
  let complement:=PlayerSpecificAlgebraicField.minus root.polynomial
    (PlayerSpecificAlgebraicField.constant root.polynomial 1) a.probability
  let h:=PlayerSpecificAlgebraicField.times root.polynomial a.third complement
  FixedArrayTable.ofFn ![u,v,w,h]

theorem positive_correct (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x) :
    positive model root a=true ↔ 0< i.a+i.d-i.B := by
  simp only [positive,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,not_le,
    PlayerSpecificAlgebraicField.plus_value _ _ _ x hx.1,ha.budget,ha.first,ha.second,sub_pos]

theorem environment_value (root : Candidate) (a : Input) (i : ThreeInput) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : Values a i x) (hE : 0< i.a+i.d-i.B) :
    PlayerSpecificAlgebraicExpression.realEnv (environment root a) x=RealThreeGeometryCode.environment (i.geometry hE) := by
  unfold PlayerSpecificAlgebraicExpression.realEnv RealThreeGeometryCode.environment
  congr 1
  funext j
  fin_cases j <;> simp [environment,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,PlayerSpecificAlgebraicField.times_value _ _ _ x hx,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx,ha.budget,ha.first,ha.second,ha.third,ha.probability,
    ThreeInput.geometry]

theorem environment_reduced (root : Candidate) (a : Input) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) :
    ∀ j,Reduced root.polynomial ((environment root a).read j) := by
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0
  · exact PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0
  · exact PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0
  · exact PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0

end Blotto.PlayerSpecificAlgebraicThreeInput
