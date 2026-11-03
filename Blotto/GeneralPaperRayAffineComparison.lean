import Blotto.GeneralPaperRayInitialQuery

/-! Exact affine differences and their unique crossings. On an open
bracket without a crossing, one interior comparison fixes the ordering
throughout. Parallel and identical functions are handled without division.
-/
namespace Blotto.GeneralPaperRayAffineComparison
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 2500000

def difference (a b : Affine) : Affine := ⟨a.intercept-b.intercept,a.slope-b.slope⟩

theorem difference_value (a b : Affine) (t : ℚ) : (difference a b).value t=a.value t-b.value t := by
  dsimp only [difference,Affine.value]
  ring

theorem negative_iff (a : Affine) (ha : a.slope<0) (t : ℚ) : a.value t≤0 ↔ a.crossing≤t := by
  rw [Affine.crossing,div_le_iff_of_neg ha]
  unfold Affine.value
  constructor <;> intro h <;> linarith only [h]

theorem crossing_zero (a : Affine) (ha : a.slope≠0) : a.value a.crossing=0 := by
  unfold Affine.value Affine.crossing
  field_simp
  ring

theorem zero_iff (a : Affine) (ha : a.slope≠0) (t : ℚ) : a.value t=0 ↔ t=a.crossing := by
  constructor
  · intro h
    have hc := crossing_zero a ha
    have he : a.slope*(t-a.crossing)=0 := by unfold Affine.value at h hc; linarith only [h,hc]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha)
  · rintro rfl
    exact crossing_zero a ha

theorem stable_nonpositive (a : Affine) (lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : a.slope≠0 → ¬(lo<a.crossing ∧ a.crossing<hi))
    (hValue : a.value sample≤0) : a.value t≤0 := by
  rcases lt_trichotomy a.slope 0 with hn|hz|hp
  · have hc := (negative_iff a hn sample).mp hValue
    have hl : a.crossing≤lo := by
      by_contra h
      exact hNoCross hn.ne ⟨lt_of_not_ge h,hc.trans_lt hSample.2⟩
    exact (negative_iff a hn t).mpr (hl.trans ht.1.le)
  · simpa only [Affine.value,hz,zero_mul,add_zero] using hValue
  · have hc := (positive_iff a hp sample).mp hValue
    have hh : hi≤a.crossing := by
      by_contra h
      exact hNoCross hp.ne' ⟨hSample.1.trans_le hc,lt_of_not_ge h⟩
    exact (positive_iff a hp t).mpr (ht.2.le.trans hh)

theorem stable_order (a b : Affine) (lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : a.slope≠b.slope → ¬(lo<(difference a b).crossing ∧ (difference a b).crossing<hi))
    (hOrder : a.value sample≤b.value sample) : a.value t≤b.value t := by
  have hh : (difference a b).value t≤0 := stable_nonpositive (difference a b) lo hi sample t hSample ht
    (fun hn => hNoCross (fun he => hn (sub_eq_zero.mpr he)))
    (by rw [difference_value]; exact sub_nonpos.mpr hOrder)
  rw [difference_value] at hh
  exact sub_nonpos.mp hh

end Blotto.GeneralPaperRayAffineComparison
