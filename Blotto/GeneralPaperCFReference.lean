import Blotto.GeneralPaperCFAdvanceData

/-! A proof-only exact rational observer for regular convergents. It uses
ordinary integer quotient/modulus as specifications; the executed query
continues to use the checked arithmetic quotient loop. This observer agrees
with the pinned Real.convergent and has positive, reduced denominators.
-/
namespace Blotto.GeneralPaperCFReference
set_option autoImplicit false
set_option maxHeartbeats 2500000

def pair (n d : ℕ) : ℕ → ℕ × ℕ
  | 0 => (n/d,1)
  | k+1 =>
    if n%d=0 then (n/d,1) else
      let tail := pair d (n%d) k
      ((n/d)*tail.1+tail.2,tail.1)

theorem floor_ratio (n d : ℕ) : ⌊((n:ℝ)/d)⌋=((n/d:ℕ):ℤ) := by
  rw [Int.floor_div_natCast,Int.floor_natCast,Int.natCast_ediv]

theorem fract_ratio (n d : ℕ) (hd : 0<d) : Int.fract ((n:ℝ)/d)=((n%d:ℕ):ℝ)/d := by
  have hd' : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have he : ((n%d:ℕ):ℝ)+(d:ℝ)*((n/d:ℕ):ℝ)=(n:ℝ) := by exact_mod_cast Nat.mod_add_div n d
  rw [Int.fract,floor_ratio,Int.cast_natCast]
  field_simp
  <;> nlinarith only [he]

theorem inverse_fract_ratio (n d : ℕ) (hd : 0<d) : (Int.fract ((n:ℝ)/d))⁻¹=(d:ℝ)/((n%d:ℕ):ℝ) := by
  rw [fract_ratio n d hd,inv_div]

theorem numerator_lower (n d k : ℕ) (hd : 0<d) : n/d≤(pair n d k).1 := by
  induction k generalizing n d with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hr : n%d=0
    · simp only [pair,ite_eq_left hr,le_refl]
    · have hp : 0<n%d := by omega
      have hQuotient : 1≤d/(n%d) := by
        apply (Nat.le_div_iff_mul_le hp).mpr
        simpa only [Nat.one_mul] using (Nat.mod_lt n hd).le
      have hTail := hQuotient.trans (ih d (n%d) hp)
      have hm := Nat.mul_le_mul_left (n/d) hTail
      simp only [pair,ite_eq_right hr]
      nlinarith only [hm]

theorem numerator_positive (n d k : ℕ) (hd : 0<d) (hOrder : d≤n) : 0<(pair n d k).1 := by
  have he : 1≤n/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.one_mul] using hOrder)
  exact lt_of_lt_of_le (by decide : 0<1) (he.trans (numerator_lower n d k hd))

theorem denominator_positive (n d k : ℕ) (hd : 0<d) : 0<(pair n d k).2 := by
  cases k with
  | zero => exact Nat.zero_lt_one
  | succ k =>
    by_cases hr : n%d=0
    · simp only [pair,ite_eq_left hr,Nat.zero_lt_one]
    · simp only [pair,ite_eq_right hr]
      exact numerator_positive d (n%d) k (by omega) (Nat.mod_lt n hd).le

theorem pair_coprime (n d k : ℕ) : Nat.Coprime (pair n d k).1 (pair n d k).2 := by
  induction k generalizing n d with
  | zero => exact Nat.coprime_one_right _
  | succ k ih =>
    by_cases hr : n%d=0
    · simpa only [pair,ite_eq_left hr] using Nat.coprime_one_right (n/d)
    · simp only [pair,ite_eq_right hr]
      have he := (Nat.coprime_add_mul_right_left (pair d (n%d) k).2 (pair d (n%d) k).1 (n/d)).mpr (ih d (n%d)).symm
      simpa only [Nat.add_comm] using he

theorem value_eq_regular (n d k : ℕ) (hd : 0<d) :
    ((pair n d k).1:ℚ)/(pair n d k).2=Real.convergent ((n:ℝ)/d) k := by
  induction k generalizing n d with
  | zero => simp only [pair,Real.convergent_zero,floor_ratio,Nat.cast_one,div_one,Int.cast_natCast]
  | succ k ih =>
    rw [Real.convergent_succ,floor_ratio,inverse_fract_ratio n d hd]
    by_cases hr : n%d=0
    · simp only [pair,ite_eq_left hr,hr,ite_true,Nat.cast_zero,div_zero,Real.convergent_of_zero,inv_zero,
        add_zero,Nat.cast_one,div_one,Int.cast_natCast]
    · have hp := numerator_positive d (n%d) k (by omega) (Nat.mod_lt n hd).le
      have hpq : ((pair d (n%d) k).1:ℚ)≠0 := by exact_mod_cast hp.ne'
      rw [←ih d (n%d) (by omega)]
      simp only [pair,ite_eq_right hr,Nat.cast_add,Nat.cast_mul,Int.cast_natCast,inv_div]
      rw [add_div,mul_div_cancel_right₀ _ hpq]

theorem reduced_denominator (n d k : ℕ) (hd : 0<d) :
    (((pair n d k).1:ℚ)/(pair n d k).2).den=(pair n d k).2 := by
  have he := Rat.den_div_eq_of_coprime (a := ((pair n d k).1:ℤ)) (b := ((pair n d k).2:ℤ))
    (by exact_mod_cast denominator_positive n d k hd) (by simpa only [Int.natAbs_natCast] using pair_coprime n d k)
  have hh : (((((pair n d k).1:ℚ)/(pair n d k).2).den:ℕ):ℤ)=((pair n d k).2:ℤ) := by
    simpa only [Int.cast_natCast] using he
  exact_mod_cast hh

end Blotto.GeneralPaperCFReference
