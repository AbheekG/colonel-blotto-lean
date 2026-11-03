import Blotto.PlayerSpecificFiniteParameterDescriptionContract

/-! Executable initial sampler lengths and mixture values in the retained
number field. One exact linear-polynomial sign chooses the marginal branch;
all subsequent rows use the actual reduced field arithmetic. A caller
computes and caches the scale inverse once for the complete input vector. -/
namespace Blotto.PlayerSpecificAlgebraicInitial
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def low (model : RationalCostModel) (candidate : Candidate) (v w : ℚ) : Bool :=
  decide ((PlayerSpecificPolynomialSignExecution.run model candidate.polynomial [v,-w] candidate.interval).1≠.pos)
def weighted (candidate : Candidate) (w : ℚ) : Data := reduce candidate.polynomial [0,w]
def numerator (model : RationalCostModel) (candidate : Candidate) (v w : ℚ) : Data :=
  if low model candidate v w then PlayerSpecificAlgebraicField.constant candidate.polynomial v else weighted candidate w
def probabilityA (model : RationalCostModel) (candidate : Candidate) (v w : ℚ) : Data :=
  if low model candidate v w then
    PlayerSpecificAlgebraicField.divide candidate.polynomial (PlayerSpecificAlgebraicField.constant candidate.polynomial v) (weighted candidate w)
  else PlayerSpecificAlgebraicField.constant candidate.polynomial 1
def probabilityB (model : RationalCostModel) (candidate : Candidate) (v w : ℚ) : Data :=
  if low model candidate v w then PlayerSpecificAlgebraicField.constant candidate.polynomial 1
  else PlayerSpecificAlgebraicField.divide candidate.polynomial (weighted candidate w) (PlayerSpecificAlgebraicField.constant candidate.polynomial v)

structure Result where
  length : Data
  initialA : Data
  initialB : Data

def run (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ) : Result :=
  let branch:=low model candidate v w
  let first:=PlayerSpecificAlgebraicField.constant candidate.polynomial v
  let second:=weighted candidate w
  let unit:=PlayerSpecificAlgebraicField.constant candidate.polynomial 1
  let minimum:=if branch then first else second
  let probA:=if branch then PlayerSpecificAlgebraicField.divide candidate.polynomial first second else unit
  let probB:=if branch then unit else PlayerSpecificAlgebraicField.divide candidate.polynomial second first
  let length:=PlayerSpecificAlgebraicField.times candidate.polynomial minimum inverseScale
  ⟨length,PlayerSpecificAlgebraicField.times candidate.polynomial probA length,
    PlayerSpecificAlgebraicField.times candidate.polynomial probB length⟩

theorem run_length (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ) :
    (run model candidate inverseScale v w).length=
      PlayerSpecificAlgebraicField.times candidate.polynomial (numerator model candidate v w) inverseScale := rfl
theorem run_initialA (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ) :
    (run model candidate inverseScale v w).initialA=PlayerSpecificAlgebraicField.times candidate.polynomial
      (probabilityA model candidate v w) (run model candidate inverseScale v w).length := rfl
theorem run_initialB (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ) :
    (run model candidate inverseScale v w).initialB=PlayerSpecificAlgebraicField.times candidate.polynomial
      (probabilityB model candidate v w) (run model candidate inverseScale v w).length := rfl

theorem linear_value (v w : ℚ) (x : ℝ) : realEvaluate [v,-w] x=(v:ℝ)-x*(w:ℝ) := by
  simp only [realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_neg,mul_zero,add_zero]
  ring
theorem weighted_value (candidate : Candidate) (w : ℚ) (x : ℝ) (hx : realEvaluate candidate.polynomial x=0) :
    realEvaluate (weighted candidate w) x=x*(w:ℝ) := by
  rw [weighted,real_reduce candidate.polynomial _ x hx]
  simp only [realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_zero,mul_zero,add_zero,zero_add]

theorem low_correct (model : RationalCostModel) (candidate : Candidate) (v w : ℚ)
    (hm : Normalized candidate.polynomial) (hirr : Irreducible (semantics candidate.polynomial))
    (hv : candidate.interval.lo<candidate.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique candidate.polynomial candidate.interval x) :
    low model candidate v w=true ↔ (v:ℝ)≤x*(w:ℝ) := by
  have hs:=PlayerSpecificPolynomialSignExecution.correct model candidate.polynomial [v,-w] candidate.interval hm hirr hv x hx
  simp only [low,decide_eq_true_eq,hs,linear_value,SignType.pos_eq_one,ne_eq,sign_eq_one_iff,not_lt,sub_nonpos]

theorem weighted_reduced (candidate : Candidate) (w : ℚ) (hm : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) :
    Reduced candidate.polynomial (weighted candidate w) := reduced _ _ hm hm0

theorem reduced_result (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ)
    (hm : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) :
    Reduced candidate.polynomial (run model candidate inverseScale v w).length ∧
      Reduced candidate.polynomial (run model candidate inverseScale v w).initialA ∧
      Reduced candidate.polynomial (run model candidate inverseScale v w).initialB := by
  exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
    PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0⟩

end Blotto.PlayerSpecificAlgebraicInitial
