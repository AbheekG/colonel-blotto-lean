import Blotto.PlayerSpecificIsolationGeometry

/-! Cubics have at most three retained root intervals and at most 6d+1
source calls at depth d. A geometric separation criterion certifies unit
counts, but computing/proving that separation and depth from coefficients
is still required; this conditional criterion does not finish isolation. -/
namespace Blotto.PlayerSpecificIsolationBounds
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificIsolationForest
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem roots_bound (p : Data) : (PlayerSpecificSturmRootCount.roots p).card≤p.length-1 := by
  have h := (Multiset.toFinset_card_le (PlayerSpecificSquarefreeAlgorithm.realPolynomial p).roots).trans
    (Polynomial.card_roots' (PlayerSpecificSquarefreeAlgorithm.realPolynomial p))
  change (PlayerSpecificSturmRootCount.roots p).card≤(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).natDegree at h
  apply h.trans
  rw [PlayerSpecificSquarefreeAlgorithm.realPolynomial,Polynomial.natDegree_map]
  exact PlayerSpecificPolynomialNormalization.degree_le p

theorem count_bound {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (node : Interval) (h : Valid prepared node) :
    node.count≤p.length-1 := by
  rw [count_eq prepared node h,PlayerSpecificSturmRootCount.exact_count p hp node.lo node.hi h.1.le]
  exact (Finset.card_filter_le _ _).trans (roots_bound p)

theorem cubic_count (c : PlayerSpecificCubic.Coefficients ℚ) (b : ℚ)
    (prepared : Prepared (cubic c b)) (hp : semantics (cubic c b)≠0) (node : Interval) (h : Valid prepared node) :
    node.count≤3 := count_bound prepared hp node h

theorem cubic_length (c : PlayerSpecificCubic.Coefficients ℚ) (b : ℚ)
    (prepared : Prepared (cubic c b)) (hp : semantics (cubic c b)≠0) (fuel : ℕ) (node : Interval) (h : Valid prepared node) :
    (run prepared fuel node).length≤3 :=
  (length_bound prepared hp fuel node h).trans (cubic_count c b prepared hp node h)

theorem cubic_visits (c : PlayerSpecificCubic.Coefficients ℚ) (b : ℚ)
    (prepared : Prepared (cubic c b)) (hp : semantics (cubic c b)≠0) (fuel : ℕ) (node : Interval) (h : Valid prepared node) :
    visits prepared fuel node≤6*fuel+1 := by
  have hv := visits_bound prepared hp fuel node h
  have hc := Nat.mul_le_mul_left (2*fuel) (cubic_count c b prepared hp node h)
  nlinarith only [hv,hc]

def Separated (p : Data) (eta : ℝ) : Prop :=
  ∀ r s : ℝ,PlayerSpecificSturmVariations.realEvaluate p r=0 →
    PlayerSpecificSturmVariations.realEvaluate p s=0 → r≠s → eta≤|r-s|

theorem contains_distance (node : Interval) (r s : ℝ) (hr : node.Contains r) (hs : node.Contains s) :
    |r-s|<(node.width : ℝ) := by
  change |r-s|<((node.hi-node.lo : ℚ) : ℝ)
  rw [Rat.cast_sub]
  apply abs_lt.mpr
  constructor <;> linarith [hr.1,hr.2,hs.1,hs.2]

theorem at_most_one {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (node : Interval) (h : Valid prepared node)
    (eta : ℝ) (hsep : Separated p eta) (hwidth : (node.width : ℝ)<eta) : node.count≤1 := by
  rw [count_eq prepared node h,PlayerSpecificSturmRootCount.exact_count p hp node.lo node.hi h.1.le]
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hr' := Finset.mem_filter.mp hr
  have hs' := Finset.mem_filter.mp hs
  by_contra hne
  have hlow := hsep r s ((PlayerSpecificSturmRootCount.mem_roots p hp r).mp hr'.1)
    ((PlayerSpecificSturmRootCount.mem_roots p hp s).mp hs'.1) hne
  have hhigh := contains_distance node r s hr'.2 hs'.2
  linarith

theorem unit_counts {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) (eta : ℝ) (hsep : Separated p eta)
    (hwidth : ((node.width/(2:ℚ)^fuel : ℚ) : ℝ)<eta) :
    ∀ leaf∈run prepared fuel node,leaf.count=1 := by
  intro leaf hleaf
  have hv := valid_positive prepared fuel node h leaf hleaf
  have hleafwidth : (leaf.width : ℝ)<eta := by
    rw [PlayerSpecificIsolationGeometry.width prepared fuel node leaf hleaf]
    exact hwidth
  have hc := at_most_one prepared hp leaf hv.1 eta hsep hleafwidth
  omega

theorem isolated_unique {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) (eta : ℝ) (hsep : Separated p eta)
    (hwidth : ((node.width/(2:ℚ)^fuel : ℚ) : ℝ)<eta) :
    ∀ leaf∈run prepared fuel node,∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ leaf.Contains x := by
  intro leaf hleaf
  exact PlayerSpecificIsolationGeometry.unique_root prepared hp fuel node h leaf hleaf
    (unit_counts prepared hp fuel node h eta hsep hwidth leaf hleaf)

end Blotto.PlayerSpecificIsolationBounds
