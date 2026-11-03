import Blotto.GeneralPaperProxyClassifierPaths

/-! Rational roots of affine integer residuals and their reciprocal-budget
form. Bounded coefficients give bounded reduced root denominators. This is
the algebraic root layer; deriving the coefficients from actual augmented
constraint determinants remains a separate required join.
-/
namespace Blotto.GeneralPaperIntegerResidualRoots
set_option autoImplicit false
set_option maxHeartbeats 2500000

def root (A B : ℤ) : ℚ := -(A:ℚ)/(B:ℚ)

theorem root_denominator (A B : ℤ) (hB : B≠0) : (root A B).den≤B.natAbs := by
  have hd := Rat.den_dvd (-A) B
  have he : Rat.divInt (-A) B=root A B := by rw [Rat.divInt_eq_div]; simp only [root,Int.cast_neg]
  rw [he] at hd
  have hn := Int.natAbs_dvd_natAbs.mpr hd
  have hdvd : (root A B).den∣B.natAbs := by simpa only [Int.natAbs_natCast] using hn
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hB) hdvd

theorem affine_zero_iff (A B : ℤ) (hB : B≠0) (t : ℚ) :
    (A:ℚ)+(B:ℚ)*t=0 ↔ t=root A B := by
  have hb : (B:ℚ)≠0 := by exact_mod_cast hB
  rw [root,eq_div_iff hb]
  constructor <;> intro h <;> linarith only [h]

theorem reciprocal_zero_iff (A B : ℤ) (hA : A≠0) (t : ℚ) (ht : t≠0) :
    (A:ℚ)+(B:ℚ)/t=0 ↔ t=root B A := by
  have ha : (A:ℚ)≠0 := by exact_mod_cast hA
  rw [root,eq_div_iff ha]
  constructor
  · intro h
    have he : (A:ℚ)*t+B=0 := by field_simp at h; nlinarith only [h]
    linarith only [he]
  · intro h
    apply (eq_neg_iff_add_eq_zero).mp
    rw [←neg_div]
    apply (eq_div_iff ht).mpr
    linarith only [h]

theorem affine_nonroot (H : ℕ) (t : ℚ) (ht : H<t.den) (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤H) :
    (A:ℚ)+(B:ℚ)*t≠0 := by
  intro he
  have hr := (affine_zero_iff A B hB t).mp he
  have hd := (root_denominator A B hB).trans hBound
  rw [←hr] at hd
  omega

theorem reciprocal_nonroot (H : ℕ) (t : ℚ) (ht : H<t.den) (ht0 : t≠0)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤H) : (A:ℚ)+(B:ℚ)/t≠0 := by
  by_cases hA : A=0
  · subst A
    simp only [Int.cast_zero,zero_add]
    exact div_ne_zero (by exact_mod_cast hB) ht0
  · intro he
    have hr := (reciprocal_zero_iff A B hA t ht0).mp he
    have hd := (root_denominator B A hA).trans hBound
    rw [←hr] at hd
    omega

theorem real_affine_zero_iff (A B : ℤ) (hB : B≠0) (t : ℝ) :
    (A:ℝ)+(B:ℝ)*t=0 ↔ t=(root A B:ℝ) := by
  have hb : (B:ℝ)≠0 := by exact_mod_cast hB
  simp only [root,Rat.cast_div,Rat.cast_neg,Rat.cast_intCast]
  rw [eq_div_iff hb]
  constructor <;> intro h <;> linarith only [h]

theorem real_reciprocal_zero_iff (A B : ℤ) (hA : A≠0) (t : ℝ) (ht : t≠0) :
    (A:ℝ)+(B:ℝ)/t=0 ↔ t=(root B A:ℝ) := by
  have ha : (A:ℝ)≠0 := by exact_mod_cast hA
  simp only [root,Rat.cast_div,Rat.cast_neg,Rat.cast_intCast]
  rw [eq_div_iff ha]
  constructor
  · intro h
    have he : (A:ℝ)*t+B=0 := by field_simp at h; nlinarith only [h]
    linarith only [he]
  · intro h
    apply (eq_neg_iff_add_eq_zero).mp
    rw [←neg_div]
    apply (eq_div_iff ht).mpr
    linarith only [h]

end Blotto.GeneralPaperIntegerResidualRoots
