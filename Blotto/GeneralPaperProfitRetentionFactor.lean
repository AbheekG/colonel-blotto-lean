import Blotto.GeneralPaperBalancedProfitRetention

/-! Exact rational retention factors for the balanced profit grid. These
are erased analysis of the constructed integer width, not runtime powers.
-/
namespace Blotto.GeneralPaperProfitRetentionFactor
set_option autoImplicit false
set_option maxHeartbeats 3500000

def factor (w : ℕ) : ℚ := 1-1/(w:ℚ)

theorem factor_nonnegative (w : ℕ) (hW : 0<w) : 0≤factor w := by
  have hw : (0:ℚ)<w := by exact_mod_cast hW
  have hw1 : (1:ℚ)≤w := by exact_mod_cast (show 1≤w by omega)
  have hd : (1:ℚ)/w≤1 := (div_le_iff₀ hw).mpr (by simpa only [one_mul] using hw1)
  unfold factor
  linarith

theorem factor_le_one (w : ℕ) : factor w≤1 := by
  have he : (0:ℚ)≤1/(w:ℚ) := by positivity
  unfold factor
  linarith

theorem factor_formula (w : ℕ) (hW : 0<w) : factor w=((w-1:ℕ):ℚ)/w := by
  have hw : (w:ℚ)≠0 := by exact_mod_cast hW.ne'
  rw [Nat.cast_sub (show 1≤w by omega),Nat.cast_one]
  unfold factor
  field_simp

theorem power_lower (g : ℚ) (hG : 0≤g) (n : ℕ) : 1-(1-g)*n≤g^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right ih hG
    have he : 0≤(1-g)^2*(n:ℚ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    push_cast
    nlinarith only [hm,he]

theorem factor_power_gap (w n : ℕ) (hW : 0<w) : 1-(n:ℚ)/w≤factor w^n := by
  have he := power_lower (factor w) (factor_nonnegative w hW) n
  convert he using 1
  unfold factor
  ring

theorem factor_power_lower (w H n : ℕ) (hWidth : 4*(H+1)≤w) (hN : n≤H+1) : (3/4:ℚ)≤factor w^n := by
  have hW : 0<w := by omega
  have hw : (0:ℚ)<w := by exact_mod_cast hW
  have hn : (4:ℚ)*n≤w := by exact_mod_cast (show 4*n≤w by omega)
  have hd : (n:ℚ)/w≤1/4 := (div_le_iff₀ hw).mpr (by linarith only [hn])
  exact (show (3/4:ℚ)≤1-(n:ℚ)/w by linarith).trans (factor_power_gap w n hW)

end Blotto.GeneralPaperProfitRetentionFactor
