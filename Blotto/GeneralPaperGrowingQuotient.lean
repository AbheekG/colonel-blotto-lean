import Blotto.GeneralPaperBucketGeometry

/-! Adaptive arithmetic quotient construction. Stop doubling as soon as the
divisor exceeds the dividend; unwind by comparisons, subtraction and doubled
integer counters. There is no floor, division or input-width primitive in the
executed routine. Fuel is a constructed cap; actual work depends on the
number of successful doublings, not that full cap.
-/
namespace Blotto.GeneralPaperGrowingQuotient
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Result where
  quotient : ℕ
  remainder : ℚ
  depth : ℕ
  work : ℕ

def run (x a : ℚ) : ℕ → Result
  | 0 => ⟨0,x,0,4⟩
  | fuel+1 =>
    if x<a then ⟨0,x,0,4⟩ else
      let higher := run x (2*a) fuel
      if a≤higher.remainder then
        ⟨2*higher.quotient+1,higher.remainder-a,higher.depth+1,higher.work+14⟩
      else ⟨2*higher.quotient,higher.remainder,higher.depth+1,higher.work+14⟩

theorem bounded_small (x a : ℚ) (ha : 0<a) (hx : x<a) (fuel : ℕ) :
    (GeneralPaperBoundedQuotient.run x a fuel).quotient=0 ∧ (GeneralPaperBoundedQuotient.run x a fuel).remainder=x := by
  induction fuel generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    have hh := ih (2*a) (by positivity) (by linarith only [hx,ha])
    simp only [GeneralPaperBoundedQuotient.run,hh.1,hh.2,ite_eq_right (not_le.mpr hx),Nat.mul_zero]
    trivial

theorem run_data (x a : ℚ) (ha : 0<a) (fuel : ℕ) :
    (run x a fuel).quotient=(GeneralPaperBoundedQuotient.run x a fuel).quotient ∧
      (run x a fuel).remainder=(GeneralPaperBoundedQuotient.run x a fuel).remainder := by
  induction fuel generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    by_cases hs : x<a
    · have hh := bounded_small x a ha hs (fuel+1)
      simp only [run,ite_eq_left hs,hh.1,hh.2,and_self]
    · have hh := ih (2*a) (by positivity)
      simp only [run,ite_eq_right hs,GeneralPaperBoundedQuotient.run,hh.1,hh.2]
      split <;> exact ⟨rfl,rfl⟩

theorem run_spec (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^fuel) :
    x=a*((run x a fuel).quotient:ℚ)+(run x a fuel).remainder ∧
      0≤(run x a fuel).remainder ∧ (run x a fuel).remainder<a := by
  rw [(run_data x a ha fuel).1,(run_data x a ha fuel).2]
  exact GeneralPaperBoundedQuotient.run_spec x a ha fuel hx hCap

theorem run_work (x a : ℚ) (fuel : ℕ) : (run x a fuel).work=14*(run x a fuel).depth+4 := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    simp only [run]
    split
    · rfl
    · split <;> dsimp only <;> rw [ih] <;> omega

theorem depth_le_fuel (x a : ℚ) (fuel : ℕ) : (run x a fuel).depth≤fuel := by
  induction fuel generalizing a with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [run]
    split
    · exact Nat.zero_le _
    · split <;> dsimp only <;> have := ih (2*a) <;> omega

theorem early_stop (x a : ℚ) (hx : x<a) (fuel : ℕ) : (run x a (fuel+1)).depth=0 ∧ (run x a (fuel+1)).work=4 := by
  simp only [run,ite_eq_left hx,and_self]

theorem actual_cap (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hCap : x<a*(2:ℚ)^fuel) :
    x<a*(2:ℚ)^(run x a fuel).depth := by
  induction fuel generalizing a with
  | zero => simpa only [run,pow_zero,mul_one] using hCap
  | succ fuel ih =>
    by_cases hs : x<a
    · simpa only [run,ite_eq_left hs,pow_zero,mul_one] using hs
    · have hc : x<(2*a)*(2:ℚ)^fuel := by rw [pow_succ] at hCap; nlinarith only [hCap]
      have hh := ih (2*a) (by positivity) hc
      simp only [run,ite_eq_right hs]
      split <;> dsimp only <;> rw [pow_succ] <;> nlinarith only [hh]

theorem depth_scale (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hDepth : 0<(run x a fuel).depth) :
    a*(2:ℚ)^((run x a fuel).depth-1)≤x := by
  induction fuel generalizing a with
  | zero => simp only [run] at hDepth; omega
  | succ fuel ih =>
    by_cases hs : x<a
    · simp only [run,ite_eq_left hs] at hDepth; omega
    · have hh : a*(2:ℚ)^(run x (2*a) fuel).depth≤x := by
        by_cases hd : (run x (2*a) fuel).depth=0
        · simpa only [hd,pow_zero,mul_one] using le_of_not_gt hs
        · have hl := ih (2*a) (by positivity) (by omega)
          have he : (2:ℚ)^((run x (2*a) fuel).depth-1)*2=(2:ℚ)^(run x (2*a) fuel).depth := by
            rw [←pow_succ]
            congr 1
            omega
          rw [←he]
          nlinarith only [hl]
      simp only [run,ite_eq_right hs]
      split <;> dsimp only <;> simpa only [Nat.add_sub_cancel] using hh

theorem quotient_actual_cap (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^fuel) :
    (run x a fuel).quotient<2^(run x a fuel).depth := by
  have hs := run_spec x a ha fuel hx hCap
  have hc := actual_cap x a ha fuel hCap
  have he : ((run x a fuel).quotient:ℚ)<(2:ℚ)^(run x a fuel).depth := by
    nlinarith only [hs.1,hs.2.1,hc,ha]
  exact_mod_cast he

theorem depth_quotient_lower (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^fuel)
    (hDepth : 0<(run x a fuel).depth) : 2^((run x a fuel).depth-1)≤(run x a fuel).quotient := by
  have hs := run_spec x a ha fuel hx hCap
  have hl := depth_scale x a ha fuel hDepth
  have he : (2:ℚ)^((run x a fuel).depth-1)<((run x a fuel).quotient:ℚ)+1 := by
    nlinarith only [hs.1,hs.2.2,hl,ha]
  have hn : 2^((run x a fuel).depth-1)<(run x a fuel).quotient+1 := by exact_mod_cast he
  omega

theorem depth_word_bound (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^fuel) :
    (run x a fuel).depth≤binaryWordWidth (run x a fuel).quotient := by
  by_cases hd : (run x a fuel).depth=0
  · rw [hd]
    exact Nat.zero_le _
  · have hl := depth_quotient_lower x a ha fuel hx hCap (by omega)
    have hp : 0<2^((run x a fuel).depth-1) := Nat.two_pow_pos _
    have hq : 0<(run x a fuel).quotient := hp.trans_le hl
    have he := (Nat.le_log2 hq.ne').mpr hl
    unfold binaryWordWidth
    omega

theorem work_word_bound (x a : ℚ) (ha : 0<a) (fuel : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^fuel) :
    (run x a fuel).work≤14*binaryWordWidth (run x a fuel).quotient+4 := by
  rw [run_work]
  have he := depth_word_bound x a ha fuel hx hCap
  omega

end Blotto.GeneralPaperGrowingQuotient
