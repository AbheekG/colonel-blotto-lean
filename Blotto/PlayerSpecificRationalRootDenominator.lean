import Blotto.PlayerSpecificIntegerPolynomial

/-! Rational-root denominator divisibility in degrees one, two and three,
proved directly from the canonical numerator/denominator and integer
coefficient identities. Negative and zero rational roots are included. -/
namespace Blotto.PlayerSpecificRationalRootDenominator
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem cancel_numerator (q : ℚ) (degree : ℕ) (a : ℤ) (h : (q.den:ℤ)∣a*q.num^degree) : q.den∣a.natAbs := by
  have hc : Int.gcd (q.den:ℤ) (q.num^degree)=1 := by
    rw [Int.gcd_def,Int.natAbs_natCast,Int.natAbs_pow]
    exact (q.reduced.pow_left degree).symm
  have hd:=Int.dvd_of_dvd_mul_left_of_gcd_one h hc
  simpa only [Int.natAbs_natCast] using (Int.natAbs_dvd_natAbs.mpr hd)

theorem linear (q : ℚ) (a0 a1 : ℤ) (hr : (a0:ℚ)+q*(a1:ℚ)=0) : q.den∣a1.natAbs := by
  have hden : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have hrep : (q.num:ℚ)=q*(q.den:ℚ) := (div_eq_iff hden).mp q.num_div_den
  have heq : (a0:ℚ)*(q.den:ℚ)+(a1:ℚ)*(q.num:ℚ)=0 := by
    calc
      _ = ((a0:ℚ)+q*(a1:ℚ))*(q.den:ℚ) := by rw [hrep]; ring
      _ = 0 := by rw [hr,zero_mul]
  have he : a0*(q.den:ℤ)+a1*q.num=0 := by exact_mod_cast heq
  apply cancel_numerator q 1 a1
  rw [pow_one]
  exact ⟨-a0,by nlinarith only [he]⟩

theorem quadratic (q : ℚ) (a0 a1 a2 : ℤ) (hr : (a0:ℚ)+q*((a1:ℚ)+q*(a2:ℚ))=0) : q.den∣a2.natAbs := by
  have hden : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have hrep : (q.num:ℚ)=q*(q.den:ℚ) := (div_eq_iff hden).mp q.num_div_den
  have heq : (a0:ℚ)*(q.den:ℚ)^2+(a1:ℚ)*(q.num:ℚ)*(q.den:ℚ)+(a2:ℚ)*(q.num:ℚ)^2=0 := by
    calc
      _ = ((a0:ℚ)+q*((a1:ℚ)+q*(a2:ℚ)))*(q.den:ℚ)^2 := by rw [hrep]; ring
      _ = 0 := by rw [hr,zero_mul]
  have he : a0*(q.den:ℤ)^2+a1*q.num*(q.den:ℤ)+a2*q.num^2=0 := by exact_mod_cast heq
  apply cancel_numerator q 2 a2
  exact ⟨-(a0*(q.den:ℤ)+a1*q.num),by nlinarith only [he]⟩

theorem cubic (q : ℚ) (a0 a1 a2 a3 : ℤ)
    (hr : (a0:ℚ)+q*((a1:ℚ)+q*((a2:ℚ)+q*(a3:ℚ)))=0) : q.den∣a3.natAbs := by
  have hden : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have hrep : (q.num:ℚ)=q*(q.den:ℚ) := (div_eq_iff hden).mp q.num_div_den
  have heq : (a0:ℚ)*(q.den:ℚ)^3+(a1:ℚ)*(q.num:ℚ)*(q.den:ℚ)^2+
      (a2:ℚ)*(q.num:ℚ)^2*(q.den:ℚ)+(a3:ℚ)*(q.num:ℚ)^3=0 := by
    calc
      _ = ((a0:ℚ)+q*((a1:ℚ)+q*((a2:ℚ)+q*(a3:ℚ))))*(q.den:ℚ)^3 := by rw [hrep]; ring
      _ = 0 := by rw [hr,zero_mul]
  have he : a0*(q.den:ℤ)^3+a1*q.num*(q.den:ℤ)^2+a2*q.num^2*(q.den:ℤ)+a3*q.num^3=0 := by exact_mod_cast heq
  apply cancel_numerator q 3 a3
  exact ⟨-(a0*(q.den:ℤ)^2+a1*q.num*(q.den:ℤ)+a2*q.num^2),by nlinarith only [he]⟩

end Blotto.PlayerSpecificRationalRootDenominator
