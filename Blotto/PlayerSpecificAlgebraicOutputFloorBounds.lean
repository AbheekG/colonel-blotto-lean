import Blotto.PlayerSpecificAlgebraicOutputFloor

/-! The executed binary search yields the exact lower dyadic cell,
including x=0, x=1 and every grid point. Each output decreases by less
than one grid step; every search uses O(P) exact comparisons. -/
namespace Blotto.PlayerSpecificAlgebraicOutputFloorBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicOutputFloor
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem index_bounds (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0 ≤ realEvaluate a x ∧ realEvaluate a x ≤ 1) :
    let q := (search root a P).1
    q ≤ 2^P ∧ (q:ℝ)/(2:ℝ)^P ≤ realEvaluate a x ∧
      realEvaluate a x < ((q+1:ℕ):ℝ)/(2:ℝ)^P := by
  let q := (search root a P).1
  have hp : (0:ℝ) < (2:ℝ)^P := pow_pos (by norm_num) _
  have hs := MonotoneCodeSearch.first_contract (2^P) (predicate root a P) (monotone root a P hm hirr hv x hx)
  change q ≤ 2^P+1 ∧ ∀ code ≤ 2^P,predicate root a P code=true ↔ q ≤ code at hs
  have hcast : ((2^P+1:ℕ):ℝ)=(2:ℝ)^P+1 := by norm_cast
  have htop : 1 < ((2^P+1:ℕ):ℝ)/(2:ℝ)^P := by
    rw [hcast]
    apply (lt_div_iff₀ hp).mpr
    linarith
  have htrue : predicate root a P (2^P)=true :=
    (predicate_correct root a P (2^P) hm hirr hv x hx).mpr (ha.2.trans_lt htop)
  have hq : q ≤ 2^P := (hs.2 _ le_rfl).mp htrue
  refine ⟨hq,?_,(predicate_correct root a P q hm hirr hv x hx).mp ((hs.2 q hq).mpr le_rfl)⟩
  by_cases hz : q=0
  · change (q:ℝ)/(2:ℝ)^P ≤ realEvaluate a x
    simpa only [hz,Nat.cast_zero,zero_div] using ha.1
  · have hprev : q-1 ≤ 2^P := by omega
    have hnot : predicate root a P (q-1) ≠ true := by
      intro he
      have hbad := (hs.2 (q-1) hprev).mp he
      omega
    have hl : ((q-1+1:ℕ):ℝ)/(2:ℝ)^P ≤ realEvaluate a x := by
      apply le_of_not_gt
      intro hlt
      exact hnot ((predicate_correct root a P (q-1) hm hirr hv x hx).mpr hlt)
    simpa only [show q-1+1=q by omega] using hl

theorem round_cast (root : Candidate) (a : Data) (P : ℕ) :
    (PlayerSpecificAlgebraicOutputFloor.round root a P:ℝ)=((search root a P).1:ℝ)/(2:ℝ)^P := by
  simp only [PlayerSpecificAlgebraicOutputFloor.round,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]

theorem round_bounds (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0 ≤ realEvaluate a x ∧ realEvaluate a x ≤ 1) :
    0 ≤ (PlayerSpecificAlgebraicOutputFloor.round root a P:ℝ) ∧
      (PlayerSpecificAlgebraicOutputFloor.round root a P:ℝ) ≤ realEvaluate a x ∧
      realEvaluate a x-(PlayerSpecificAlgebraicOutputFloor.round root a P:ℝ) < 1/(2:ℝ)^P := by
  have h := index_bounds root a P hm hirr hv x hx ha
  dsimp only at h
  have he : (((search root a P).1+1:ℕ):ℝ)/(2:ℝ)^P=
      ((search root a P).1:ℝ)/(2:ℝ)^P+1/(2:ℝ)^P := by
    push_cast
    rw [add_div]
  rw [he] at h
  rw [round_cast]
  exact ⟨div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _),h.2.1,by linarith only [h.2.2]⟩

theorem zero (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : realEvaluate a x=0) : PlayerSpecificAlgebraicOutputFloor.round root a P=0 := by
  have hb := round_bounds root a P hm hirr hv x hx (by rw [ha]; exact ⟨le_rfl,zero_le_one⟩)
  have he : (PlayerSpecificAlgebraicOutputFloor.round root a P:ℝ)=0 := le_antisymm (hb.2.1.trans_eq ha) hb.1
  exact_mod_cast he

theorem visits (root : Candidate) (a : Data) (P : ℕ) : (search root a P).2 ≤ P+2 := by
  have h := MonotoneCodeSearch.first_visits (2^P) (predicate root a P)
  have hp : 2^P+1 ≤ 2^(P+1) := by
    rw [pow_succ]
    have hpos := Nat.two_pow_pos P
    omega
  have hw := binaryWordWidth_mono hp
  simp only [binaryWordWidth,Nat.log2_two_pow] at hw
  exact h.trans hw

end Blotto.PlayerSpecificAlgebraicOutputFloorBounds
