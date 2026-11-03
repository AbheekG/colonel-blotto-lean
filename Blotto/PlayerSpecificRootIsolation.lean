import Blotto.PlayerSpecificRootSeparation

/-! Complete executable root isolation for nonzero rational polynomials
stored with at most four coefficients. Both the initial interval and the
finite bisection depth are computed from the input. No supplied root,
separation, precision or sign oracle is required. Polynomial bit costs
of the computed certificates and traversal are separate obligations. -/
namespace Blotto.PlayerSpecificRootIsolation
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRootMagnitude
open PlayerSpecificRootSeparation
set_option autoImplicit false
set_option maxHeartbeats 5000000

def depth (p : Data) : ℕ := binaryWordWidth (2*rootBound p*separationDenominator p)

def run (p : Data) : List Interval :=
  let prepared := prepare p
  PlayerSpecificIsolationForest.run prepared (depth p) (PlayerSpecificRootMagnitude.initial p prepared)

theorem sufficient_width (p : Data) (prepared : Prepared p) :
    (((PlayerSpecificRootMagnitude.initial p prepared).width/(2:ℚ)^depth p : ℚ):ℝ)<
      (1:ℝ)/(separationDenominator p:ℝ) := by
  have hp : (0:ℝ)<(2:ℝ)^depth p := pow_pos (by norm_num) _
  have hd : (0:ℝ)<(separationDenominator p:ℝ) := by exact_mod_cast separationDenominator_pos p
  have he : (((PlayerSpecificRootMagnitude.initial p prepared).width/(2:ℚ)^depth p : ℚ):ℝ)=
      2*(rootBound p:ℝ)/(2:ℝ)^depth p := by
    simp only [PlayerSpecificRootMagnitude.initial,PlayerSpecificIsolationState.initial,Interval.width,
      Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_neg,Rat.cast_natCast]
    congr 1
    ring
  rw [he,div_lt_div_iff₀ hp hd]
  have h := lt_pow_binaryWordWidth (2*rootBound p*separationDenominator p)
  have hh : (2:ℝ)*(rootBound p:ℝ)*(separationDenominator p:ℝ)<(2:ℝ)^depth p := by exact_mod_cast h
  simpa only [one_mul] using hh

theorem valid_positive (p : Data) : ∀ leaf∈run p,Valid (prepare p) leaf ∧ 0<leaf.count :=
  PlayerSpecificIsolationForest.valid_positive (prepare p) (depth p) _ (initial_valid p (prepare p))

theorem counts_one (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    ∀ leaf∈run p,leaf.count=1 :=
  PlayerSpecificIsolationBounds.unit_counts (prepare p) hp (depth p) _ (initial_valid p (prepare p)) _
    (separated p hp hlen) (sufficient_width p (prepare p))

theorem unique_roots (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    ∀ leaf∈run p,∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ leaf.Contains x :=
  PlayerSpecificIsolationBounds.isolated_unique (prepare p) hp (depth p) _ (initial_valid p (prepare p)) _
    (separated p hp hlen) (sufficient_width p (prepare p))

theorem covers (p : Data) (hp : semantics p≠0) (x : ℝ)
    (hx : PlayerSpecificSturmVariations.realEvaluate p x=0) : ∃ leaf∈run p,leaf.Contains x :=
  (PlayerSpecificIsolationForest.coverage (prepare p) hp (depth p) _ (initial_valid p (prepare p)) x hx).mp
    (initial_covers p hp (prepare p) x hx)

theorem disjoint (p : Data) (left right : Interval) (hl : left∈run p) (hr : right∈run p)
    (hne : left≠right) (x : ℝ) : ¬(left.Contains x ∧ right.Contains x) := by
  rintro ⟨hxl,hxr⟩
  exact hne (PlayerSpecificIsolationGeometry.same_at_point (prepare p) (depth p) _ (initial_valid p (prepare p))
    left hl right hr x hxl hxr)

theorem length_le_three (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) : (run p).length≤3 := by
  have h := (PlayerSpecificIsolationForest.length_bound (prepare p) hp (depth p) _ (initial_valid p (prepare p))).trans
    (PlayerSpecificIsolationBounds.count_bound (prepare p) hp _ (initial_valid p (prepare p)))
  change (run p).length≤p.length-1 at h
  omega

theorem visit_bound (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    PlayerSpecificIsolationForest.visits (prepare p) (depth p) (PlayerSpecificRootMagnitude.initial p (prepare p))≤6*depth p+1 := by
  have hv := PlayerSpecificIsolationForest.visits_bound (prepare p) hp (depth p) _ (initial_valid p (prepare p))
  have hc := PlayerSpecificIsolationBounds.count_bound (prepare p) hp _ (initial_valid p (prepare p))
  have hc' : (PlayerSpecificRootMagnitude.initial p (prepare p)).count≤3 := by omega
  have hm := Nat.mul_le_mul_left (2*depth p) hc'
  nlinarith only [hv,hm]

end Blotto.PlayerSpecificRootIsolation
