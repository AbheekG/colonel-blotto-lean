import Blotto.PlayerSpecificReconstructionLeafCost

/-! Every returned rational root has linear original-input numerator and
denominator height. This also bounds exact linear factors and row copies. -/
namespace Blotto.PlayerSpecificRationalRootHeight
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 3000000

def height (p : Data) : ℕ := 7*inputHeight p+2

theorem root_height (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (q : ℚ) (hq : evaluate p q=0) : RationalHeight q (height p) := by
  let H:=inputHeight p
  let M:=PlayerSpecificRootMagnitude.rootBound p
  have hroot : PlayerSpecificSturmVariations.realEvaluate p (q:ℝ)=0 := by
    rw [PlayerSpecificSturmVariations.evaluate_cast,hq,Rat.cast_zero]
  have hm : |(q:ℝ)|<(M:ℝ) := PlayerSpecificRootMagnitude.root_lt p hp (q:ℝ) hroot
  have hd:=PlayerSpecificRationalRootBound.denominator_lt p hp hlen q hq
  change q.den<2^(5*H) at hd
  have hdR : (q.den:ℝ)<(2:ℝ)^(5*H) := by exact_mod_cast hd
  have hdpos : (0:ℝ)<q.den := by exact_mod_cast q.den_pos
  have hrepQ : (q.num:ℚ)=q*(q.den:ℚ) := (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have hrep : (q.num:ℝ)=(q:ℝ)*(q.den:ℝ) := by exact_mod_cast hrepQ
  have habs : (q.num.natAbs:ℝ)=|(q:ℝ)| *(q.den:ℝ) := by
    rw [Nat.cast_natAbs,Int.cast_abs,hrep,abs_mul,abs_of_pos hdpos]
  have hmul:=(mul_lt_mul_of_pos_right hm hdpos).trans_le
    (mul_le_mul_of_nonneg_left hdR.le (Nat.cast_nonneg M))
  have hMpower : (M:ℝ)=(2:ℝ)^(2*H+2) := by
    simp only [M,H,PlayerSpecificRootMagnitude.rootBound,Nat.cast_pow,Nat.cast_ofNat]
  have hn : (q.num.natAbs:ℝ)<(2:ℝ)^(7*H+2) := by
    rw [←habs,hMpower,←pow_add] at hmul
    simpa only [show (2*H+2)+5*H=7*H+2 by omega] using hmul
  constructor
  · exact_mod_cast hn
  · exact hd.trans_le (Nat.pow_le_pow_right (by decide) (by unfold height; omega))

end Blotto.PlayerSpecificRationalRootHeight
