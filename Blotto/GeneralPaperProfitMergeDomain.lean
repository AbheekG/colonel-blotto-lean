import Blotto.GeneralPaperProfitTreeBounds

/-! A positive integer input profit has the paper's 1/q gap. The constructed
grid exponent and balanced-tree width keep positive intermediate sums within
the relative-rounding domain, before applying any further rounding lemma.
-/
namespace Blotto.GeneralPaperProfitMergeDomain
open GeneralPaperProfitGridPoints GeneralPaperProfitRetentionFactor GeneralPaperProfitRationalRound
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem positive_leaf_domain (q B P : ℕ) (hExponent : 4*q≤2^B) (hP : 0<P) : q≤P*2^B := by
  have he := Nat.mul_le_mul_right (2^B) (show 1≤P by omega)
  simp only [Nat.one_mul] at he
  omega

theorem positive_merge_domain (q w B H n P S : ℕ) (hQ : 0<q) (hWidth : 4*(H+1)≤w)
    (hExponent : 4*q≤2^B) (hN : n≤H+1) (hP : 0<P)
    (hDominance : factor w^n*profit q P≤(S:ℚ)/(denominator w B:ℚ)) : w≤S := by
  have hW : 0<w := by omega
  have hq : (0:ℚ)<q := by exact_mod_cast hQ
  have hf : (0:ℚ)<denominator w B := by exact_mod_cast denominator_positive w B hW
  have hg := factor_power_lower w H n hWidth hN
  have hp : (1:ℚ)/q≤profit q P := div_le_div_of_nonneg_right (by exact_mod_cast (show 1≤P by omega)) hq.le
  have hgn : (0:ℚ)≤factor w^n := pow_nonneg (factor_nonnegative w hW) n
  have hGap : (3:ℚ)/(4*q)≤(S:ℚ)/(denominator w B:ℚ) := by
    calc
      _ = (3/4:ℚ)*(1/(q:ℚ)) := by ring
      _ ≤ factor w^n*profit q P := mul_le_mul hg hp (by positivity) hgn
      _ ≤ _ := hDominance
  have hCross := (div_le_div_iff₀ (show (0:ℚ)<4*q by positivity) hf).mp hGap
  have hScale : (4:ℚ)*q*w≤(denominator w B:ℚ) := by
    have he := Nat.mul_le_mul_right w hExponent
    exact_mod_cast he
  have hTimes : ((4:ℚ)*q)*(3*(w:ℚ))≤((4:ℚ)*q)*(S:ℚ) := by nlinarith only [hCross,hScale]
  have hs : (3:ℚ)*w≤S := (mul_le_mul_iff_right₀ (show (0:ℚ)<4*q by positivity)).mp hTimes
  have hn : 3*w≤S := by exact_mod_cast hs
  omega

end Blotto.GeneralPaperProfitMergeDomain
