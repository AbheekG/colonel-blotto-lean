import Blotto.PlayerSpecificInitialMinimumContract

/-! Actual exact tests for fractional algebraic resource coordinates.
All runtime arguments are finite rational-coefficient/root data; the
selected real root occurs only in the correctness theorem. -/
namespace Blotto.PlayerSpecificAlgebraicActive
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (length value : Data) : Bool :=
  (!PlayerSpecificAlgebraicPairStep.le model root value []) && (!PlayerSpecificAlgebraicPairStep.le model root length value)

theorem correct (model : RationalCostModel) (root : Candidate) (length value : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    run model root length value=true ↔ 0<realEvaluate value x ∧ realEvaluate value x<realEvaluate length x := by
  have hz:=PlayerSpecificAlgebraicPairStep.le_correct model root value [] hm hirr hv x hx
  have hl:=PlayerSpecificAlgebraicPairStep.le_correct model root length value hm hirr hv x hx
  have he : realEvaluate [] x=0 := rfl
  simp only [run,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,hz,hl,he,not_le]

end Blotto.PlayerSpecificAlgebraicActive
