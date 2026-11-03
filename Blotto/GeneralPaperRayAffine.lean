import Blotto.GeneralPaperSourceInitializer

/-! Exact rational affine residuals on a basis-search ray. Positive slopes
give their actual crossing time; nonpositive slopes impose no restriction
on forward time from a feasible start. Zero-length endpoints are included.
-/
namespace Blotto.GeneralPaperRayAffine
set_option autoImplicit false

structure Affine where
  intercept : ℚ
  slope : ℚ

def Affine.value (a : Affine) (t : ℚ) : ℚ := a.intercept+a.slope*t

def Affine.crossing (a : Affine) : ℚ := -a.intercept/a.slope

theorem positive_iff (a : Affine) (ha : 0<a.slope) (t : ℚ) : a.value t≤0 ↔ t≤a.crossing := by
  rw [Affine.crossing,le_div_iff₀ ha]
  unfold Affine.value
  constructor <;> intro h <;> linarith only [h]

theorem crossing_nonnegative (a : Affine) (hStart : a.intercept≤0) (ha : 0<a.slope) : 0≤a.crossing :=
  div_nonneg (neg_nonneg.mpr hStart) ha.le

theorem crossing_tight (a : Affine) (ha : 0<a.slope) : a.value a.crossing=0 := by
  unfold Affine.value Affine.crossing
  field_simp
  ring

theorem nonpositive_forward (a : Affine) (hStart : a.intercept≤0) (ha : a.slope≤0) (t : ℚ) (ht : 0≤t) :
    a.value t≤0 := by
  have hp := mul_nonpos_of_nonpos_of_nonneg ha ht
  unfold Affine.value
  linarith only [hStart,hp]

theorem beyond_crossing (a : Affine) (ha : 0<a.slope) (t : ℚ) (ht : a.crossing<t) : 0<a.value t := by
  exact lt_of_not_ge (fun h => (not_le_of_gt ht) ((positive_iff a ha t).mp h))

end Blotto.GeneralPaperRayAffine
