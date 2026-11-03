import Blotto.GeneralPaperRayFixedTuple

/-! A feasible left endpoint, a strict interior violation and absence of
interior residual roots force an original positive-slope tight blocker.
The argument includes a left endpoint zero and requires no strict start.
-/
namespace Blotto.GeneralPaperRayBlockerAlgebra
open GeneralPaperRayAffine GeneralPaperRayAffineComparison
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem positive_blocker (a : Affine) (lo hi sample : ℚ) (hSample : lo<sample ∧ sample<hi)
    (hLeft : a.value lo≤0) (hViolation : 0<a.value sample)
    (hNoCross : a.slope≠0 → ¬(lo<a.crossing ∧ a.crossing<hi)) :
    0<a.slope ∧ a.value lo=0 ∧ ∀ t,lo<t → 0<a.value t := by
  have hd : a.value sample-a.value lo=a.slope*(sample-lo) := by unfold Affine.value; ring
  have hp : 0<a.slope := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sub_nonneg.mpr hSample.1.le)
    linarith only [hd,hLeft,hViolation,hm]
  have hLower := (positive_iff a hp lo).mp hLeft
  have hUpper : a.crossing<sample := by
    by_contra hn
    have hNonpos := (positive_iff a hp sample).mpr (le_of_not_gt hn)
    exact (not_lt_of_ge hNonpos) hViolation
  have hEq : a.crossing=lo := by
    apply le_antisymm _ hLower
    by_contra hn
    exact hNoCross hp.ne' ⟨lt_of_not_ge hn,hUpper.trans hSample.2⟩
  exact ⟨hp,by rw [←hEq]; exact crossing_tight a hp,fun t ht => beyond_crossing a hp t (by rwa [hEq])⟩

theorem slope_equal (a b : Affine) (hAll : ∀ t,a.value t=b.value t) : a.slope=b.slope := by
  have h0 := hAll 0
  have h1 := hAll 1
  simp only [Affine.value,mul_zero,add_zero,mul_one] at h0 h1
  linarith only [h0,h1]

end Blotto.GeneralPaperRayBlockerAlgebra
