import Blotto.PlayerSpecificAlgebraicNestedSecondSizes

/-! Whole-reference transports avoid re-expanding cached arithmetic when
an evaluated algebraic parameter equals its real paper parameter. -/
namespace Blotto.PlayerSpecificAlgebraicNestedProfileTransport
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem family_congr (i : NestedInput) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hsv : s ≤ i.v) (htv : t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) (he : s=t) :
    PlayerSpecificAlgebraicNestedFamilyReference.reference i s hs hsv K outer =
      PlayerSpecificAlgebraicNestedFamilyReference.reference i t ht htv K outer := by
  cases he
  rfl

theorem family_refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (short : Data) (T : ℕ) (hfit : Fits root a T)
    (hshort : Reduced root.polynomial short ∧ HasHeight short T) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (s : ℝ) (hs : 0 < s) (hsv : s ≤ i.v)
    (he : realEvaluate short x=s) (K : ℕ) (outer : Fin K → Bool) :
    Refines (PlayerSpecificAlgebraicNestedFamily.profile model root a short K outer) x
      (PlayerSpecificAlgebraicNestedFamilyReference.reference i s hs hsv K outer) := by
  have hs' : 0 < realEvaluate short x := by rw [he]; exact hs
  have hsv' : realEvaluate short x ≤ i.v := by rw [he]; exact hsv
  have hr := PlayerSpecificAlgebraicNestedFamilyReference.refines model root a i hm hirr hv x hx ha short T
    hfit hshort hml hmT hT hs' hsv' K outer
  exact family_congr i _ s hs' hs hsv' hsv K outer he ▸ hr

theorem binary_congr {N k m : ℕ} (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (l : SegmentLottery N k) (r : SegmentLottery N m) (he : p=q) :
    PlayerSpecificSegmentAssemblyReference.binary p hp l r = PlayerSpecificSegmentAssemblyReference.binary q hq l r := by
  cases he
  rfl

theorem binary_refines {N k m : ℕ} (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (he : realEvaluate p x=q)
    (lref : SegmentLottery N k) (rref : SegmentLottery N m) (hl : Refines l x lref) (hr : Refines r x rref) :
    Refines (PlayerSpecificAlgebraicDescriptorBinary.binary root p l r) x
      (PlayerSpecificSegmentAssemblyReference.binary q hq lref rref) := by
  have hp : 0 ≤ realEvaluate p x ∧ realEvaluate p x ≤ 1 := by rw [he]; exact hq
  have hb := PlayerSpecificAlgebraicDescriptorBinary.refines root p l r x hx hp lref rref hl hr
  exact binary_congr _ q hp hq lref rref he ▸ hb

end Blotto.PlayerSpecificAlgebraicNestedProfileTransport
