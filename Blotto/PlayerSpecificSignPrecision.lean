import Blotto.PlayerSpecificSignEnclosure

/-! Computed sufficient sign precision: the actual width of a product of
the endpoint enclosure, Lipschitz constant and unit-certificate bound. -/
namespace Blotto.PlayerSpecificSignPrecision
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificAlgebraicSignMagnitude
set_option autoImplicit false
set_option maxHeartbeats 1500000

def depth (m a : Data) (node : Interval) : ℕ :=
  let M:=PlayerSpecificSignEnclosure.magnitude node
  binaryWordWidth (8*M*lipschitz a M*gapDenominator m a M)

theorem profile (M L B W T : ℝ) (_hM : 0≤M) (hL : 0<L) (hB : 0<B)
    (hW : W≤2*M) (hT : 0<T) (hbig : 8*M*L*B<T) : L*(W/T)<1/(4*B) := by
  have hs:=mul_le_mul_of_nonneg_left hW (show 0≤4*B*L by positivity)
  have hm : (4*B)*(L*W)<T := by nlinarith only [hs,hbig]
  apply (lt_div_iff₀ (show 0<4*B by positivity)).mpr
  calc
    _ = ((4*B)*(L*W))/T := by ring
    _ < 1 := (div_lt_one hT).mpr hm

theorem sufficient_width (m a : Data) (node : Interval) :
    (lipschitz a (PlayerSpecificSignEnclosure.magnitude node):ℝ)*
      ((node.width/(2:ℚ)^depth m a node:ℚ):ℝ)<
        (1:ℝ)/(4*(gapDenominator m a (PlayerSpecificSignEnclosure.magnitude node):ℝ)) := by
  let M:=PlayerSpecificSignEnclosure.magnitude node
  have hbig : (8:ℝ)*(M:ℝ)*(lipschitz a M:ℝ)*(gapDenominator m a M:ℝ)<(2:ℝ)^depth m a node := by
    exact_mod_cast lt_pow_binaryWordWidth (8*M*lipschitz a M*gapDenominator m a M)
  have hp:=profile (M:ℝ) (lipschitz a M:ℝ) (gapDenominator m a M:ℝ) (node.width:ℝ) ((2:ℝ)^depth m a node)
    (Nat.cast_nonneg _) (by exact_mod_cast lipschitz_positive a M) (by exact_mod_cast gap_positive m a M)
    (PlayerSpecificSignEnclosure.width_bound node) (pow_pos (by norm_num) _) hbig
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hp

end Blotto.PlayerSpecificSignPrecision
