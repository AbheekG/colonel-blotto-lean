import Blotto.PlayerSpecificAlgebraicExpressionHeights
import Blotto.Boxes

/-! Cached finite segment descriptors and actual algebraic interpolation.
Both scalar coefficient rows are built once per reached segment draw. -/
namespace Blotto.PlayerSpecificAlgebraicSegment
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Descriptor (N slots : ℕ) where
  weights : FixedArrayTable slots Data
  first : FixedArrayTable slots (FixedArrayTable N Data)
  second : FixedArrayTable slots (FixedArrayTable N Data)

def interpolate {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ) : FixedArrayTable N Data :=
  let left:=PlayerSpecificAlgebraicField.constant root.polynomial (1-q)
  let right:=PlayerSpecificAlgebraicField.constant root.polynomial q
  FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicField.plus root.polynomial
    (PlayerSpecificAlgebraicField.times root.polynomial left ((d.first.read slot).read j))
    (PlayerSpecificAlgebraicField.times root.polynomial right ((d.second.read slot).read j)))

noncomputable def values {N : ℕ} (a : FixedArrayTable N Data) (x : ℝ) : Allocation N := fun j => realEvaluate (a.read j) x

theorem interpolate_value {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    values (interpolate root d slot q) x=segmentPoint (values (d.first.read slot) x) (values (d.second.read slot) x) q := by
  funext j
  simp only [values,interpolate,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicField.plus_value _ _ _ x hx,
    PlayerSpecificAlgebraicField.times_value _ _ _ x hx,PlayerSpecificAlgebraicField.constant_value _ _ x hx,
    Rat.cast_sub,Rat.cast_one,segmentPoint]

theorem interpolate_budget {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ)
    (x B : ℝ) (hx : realEvaluate root.polynomial x=0) (hq : 0≤q ∧ q≤1)
    (hP : FullBudget B (values (d.first.read slot) x)) (hQ : FullBudget B (values (d.second.read slot) x)) :
    FullBudget B (values (interpolate root d slot q) x) := by
  rw [interpolate_value root d slot q x hx]
  exact segment_fullBudget hP hQ (by exact_mod_cast hq)

theorem interpolate_box {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ)
    (x : ℝ) (length : Allocation N) (hx : realEvaluate root.polynomial x=0) (hq : 0≤q ∧ q≤1)
    (hP : InBox length (values (d.first.read slot) x)) (hQ : InBox length (values (d.second.read slot) x)) :
    InBox length (values (interpolate root d slot q) x) := by
  rw [interpolate_value root d slot q x hx]
  exact segment_inBox hP hQ (by exact_mod_cast hq)

end Blotto.PlayerSpecificAlgebraicSegment
