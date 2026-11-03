import Blotto.GeneralPaperInitializerRounding

/-! Derived rational root separation for the actual auxiliary grid.
The proxy representation is allowed to be unreduced. Every distinct root
with denominator<=H is at distance at least 4*tau from beta0, so the whole
closed interval [beta_aux,beta0] is root-free when beta0 is not a root.
-/
namespace Blotto.GeneralPaperInitializerRootGap
open GeneralPaperInitializerParameters
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem positive_difference (x y : ℚ) (D E : ℕ) (_hD : 0<D) (_hE : 0<E)
    (hx : x.den≤D) (hy : y.den≤E) (h : x<y) : 1/((D:ℚ)*E)≤y-x := by
  have hd : (y-x).den≤D*E := by
    have hb := Nat.le_of_dvd (Nat.mul_pos y.den_pos x.den_pos) (Rat.sub_den_dvd y x)
    exact hb.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hy hx)
  have hq : ((y-x).den:ℚ)≤(D:ℚ)*E := by exact_mod_cast hd
  exact (one_div_le_one_div_of_le (by positivity : (0:ℚ)<(y-x).den) hq).trans
    (Farey.positive_rational_den_gap _ (sub_pos.mpr h))

theorem separation (x y : ℚ) (D E : ℕ) (hD : 0<D) (hE : 0<E)
    (hx : x.den≤D) (hy : y.den≤E) (hne : x≠y) : 1/((D:ℚ)*E)≤|x-y| := by
  rcases lt_or_gt_of_ne hne with h|h
  · have hg := positive_difference x y D E hD hE hx hy h
    rw [abs_of_neg (sub_neg.mpr h)]
    linarith only [hg]
  · have hg := positive_difference y x E D hE hD hy hx h
    rw [abs_of_pos (sub_pos.mpr h)]
    simpa only [mul_comm] using hg

def proxyDenominator (p q : ℕ) (reciprocal : Bool) : ℕ := if reciprocal then p else q

theorem beta_denominator (m H p q : ℕ) (reciprocal : Bool) (hp : 0<p) (hq : 0<q) :
    (prepare m H p q reciprocal).beta.den≤proxyDenominator p q reciprocal := by
  cases reciprocal
  · exact (reduced_fraction_bounds (p:ℤ) q hq).2
  · exact (reduced_fraction_bounds (q:ℤ) p hp).2

theorem four_tau (m H p q : ℕ) (reciprocal : Bool) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    4*(prepare m H p q reciprocal).tau≤1/((proxyDenominator p q reciprocal:ℕ):ℚ)/(H:ℚ) := by
  rw [tau_exact m H p q reciprocal hm,div_div]
  have hpp : (1:ℚ)≤p := by exact_mod_cast hp
  have hqq : (1:ℚ)≤q := by exact_mod_cast hq
  have hhh : (0:ℚ)<H := by exact_mod_cast hH
  cases reciprocal <;> simp only [proxyDenominator,Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp
  all_goals nlinarith

theorem gap (m H p q : ℕ) (reciprocal : Bool) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q)
    (root : ℚ) (hRoot : root.den≤H) (hne : (prepare m H p q reciprocal).beta≠root) :
    4*(prepare m H p q reciprocal).tau≤|(prepare m H p q reciprocal).beta-root| := by
  have hd : 0<proxyDenominator p q reciprocal := by cases reciprocal <;> simp only [proxyDenominator,Bool.false_eq_true,ite_false,ite_true] <;> assumption
  have hs := separation (prepare m H p q reciprocal).beta root (proxyDenominator p q reciprocal) H hd hH
    (beta_denominator m H p q reciprocal hp hq) hRoot hne
  have ht := four_tau m H p q reciprocal hm hH hp hq
  rw [div_div] at ht
  exact ht.trans hs

theorem excludes_auxiliary_interval (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q)
    (root : ℚ) (hRoot : root.den≤H) (hne : (prepare m H p q reciprocal).beta≠root) :
    ¬((prepare m H p q reciprocal).auxiliary≤root ∧ root≤(prepare m H p q reciprocal).beta) := by
  intro hc
  have hg := gap m H p q reciprocal hm hH hp hq root hRoot hne
  rw [abs_of_nonneg (sub_nonneg.mpr hc.2)] at hg
  have ht := tau_positive m H p q reciprocal hm hH hp hq
  have ha := (data m H p q reciprocal).2.2.2
  linarith only [hg,hc.1,ht,ha]

end Blotto.GeneralPaperInitializerRootGap
