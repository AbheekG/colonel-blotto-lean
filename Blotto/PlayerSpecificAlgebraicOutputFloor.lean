import Blotto.PlayerSpecificFiniteAccuracy
import Blotto.MonotoneCodeSearch

/-! Actual downward rational output uses binary search and exact selected-
root comparisons. The monotone predicate is x < (code+1)/2^P, so the
returned first code is the floor even at dyadic grid points and zero. -/
namespace Blotto.PlayerSpecificAlgebraicOutputFloor
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def threshold (P code : ℕ) : ℚ := (code+1:ℕ)/(2:ℚ)^P

def predicate (root : Candidate) (a : Data) (P code : ℕ) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le RationalCostModel.schoolbook root
    (PlayerSpecificAlgebraicField.constant root.polynomial (threshold P code)) a

def search (root : Candidate) (a : Data) (P : ℕ) : ℕ × ℕ :=
  MonotoneCodeSearch.first (2^P) (predicate root a P)

def round (root : Candidate) (a : Data) (P : ℕ) : ℚ := (search root a P).1/(2:ℚ)^P

theorem threshold_cast (P code : ℕ) : (threshold P code:ℝ)=((code+1:ℕ):ℝ)/(2:ℝ)^P := by
  simp only [threshold,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]

theorem predicate_correct (root : Candidate) (a : Data) (P code : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    predicate root a P code=true ↔ realEvaluate a x < ((code+1:ℕ):ℝ)/(2:ℝ)^P := by
  simp only [predicate,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct RationalCostModel.schoolbook root _ _ hm hirr hv x hx,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx.1,threshold_cast,not_le]

theorem monotone (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    MonotoneCodeSearch.IsMonotone (2^P) (predicate root a P) := by
  intro first second hle _ hfirst
  apply (predicate_correct root a P second hm hirr hv x hx).mpr
  apply ((predicate_correct root a P first hm hirr hv x hx).mp hfirst).trans_le
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by norm_num) _)
  exact_mod_cast Nat.add_le_add_right hle 1

end Blotto.PlayerSpecificAlgebraicOutputFloor
