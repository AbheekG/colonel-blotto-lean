import Blotto.GeneralPaperScoreDPBits

/-! Actual quotient/remainder sizes. The exact affine invariant represents
the current remainder as x-a*q, avoiding exponential height loss from
repeated subtraction. A common linear height covers every recursive level.
-/
namespace Blotto.GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem nat_height (n s : ℕ) (hn : n<2^s) : RationalHeight (n:ℚ) (s+1) := by
  simp only [RationalHeight,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast]
  constructor
  · exact hn.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_succ s))
  · have hp : 0<(2:ℕ)^s := Nat.two_pow_pos s
    rw [pow_succ]
    omega

theorem quotient_lt (x a : ℚ) (ha : 0<a) (w : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^w) :
    (run x a w).quotient<2^w := by
  have hs := run_spec x a ha w hx hCap
  have hl : a*((run x a w).quotient:ℚ)≤x := by linarith only [hs.1,hs.2.1]
  have hq : ((run x a w).quotient:ℚ)<(2:ℚ)^w := by
    nlinarith only [hl,hCap,ha]
  exact_mod_cast hq

theorem remainder_height (x a : ℚ) (ha : 0<a) (w A t : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^w)
    (hX : RationalHeight x A) (hA : RationalHeight a t) :
    RationalHeight (run x a w).remainder (A+t+w+2) := by
  have hq := nat_height (run x a w).quotient w (quotient_lt x a ha w hx hCap)
  have hs := run_spec x a ha w hx hCap
  have he : (run x a w).remainder=x-a*((run x a w).quotient:ℚ) := by linarith only [hs.1]
  rw [he]
  exact (hX.sub (hA.mul hq)).mono (by omega)

def heightBudget (A t w : ℕ) : ℕ := A+t+2*w+4

theorem budget_step (A t w : ℕ) : heightBudget A (t+2) w=heightBudget A t (w+1) := by
  unfold heightBudget
  omega

theorem remainder_common (x a : ℚ) (ha : 0<a) (w A t : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^w)
    (hX : RationalHeight x A) (hA : RationalHeight a t) :
    RationalHeight (run x a w).remainder (heightBudget A t w) :=
  (remainder_height x a ha w A t hx hCap hX hA).mono (by unfold heightBudget; omega)

theorem doubled_height (a : ℚ) (t : ℕ) (hA : RationalHeight a t) : RationalHeight (2*a) (t+2) := by
  have h2 : RationalHeight 2 2 := by norm_num [RationalHeight]
  simpa only [Nat.add_comm] using h2.mul hA

theorem higher_remainder_common (x a : ℚ) (ha : 0<a) (w A t : ℕ) (hx : 0≤x)
    (hCap : x<a*(2:ℚ)^(w+1)) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    RationalHeight (run x (2*a) w).remainder (heightBudget A t (w+1)) := by
  have hc : x<(2*a)*(2:ℚ)^w := by rw [pow_succ] at hCap; nlinarith only [hCap]
  rw [← budget_step]
  exact remainder_common x (2*a) (by positivity) w A (t+2) hx hc hX (doubled_height a t hA)

theorem quotient_words (x a : ℚ) (ha : 0<a) (w : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^w) :
    binaryWordWidth (run x a w).quotient ≤ w+1 :=
  binaryWordWidth_le_of_lt_pow (by omega)
    ((quotient_lt x a ha w hx hCap).trans_le
      (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_succ w)))

end Blotto.GeneralPaperBoundedQuotient
