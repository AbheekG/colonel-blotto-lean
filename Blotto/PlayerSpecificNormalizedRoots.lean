import Blotto.PlayerSpecificRootCells

/-! Affine normalization preserves rational-root denominator bounds and
puts the actual dyadic leaf into the closed CF-query cell. -/
namespace Blotto.PlayerSpecificNormalizedRoots
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRootCells
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem denominator_bound (M : ℕ) (hM : 0<M) (q : ℚ) : (normalized M q).den≤q.den*(2*M) := by
  have hsum : OnRationalLattice q.den (q+(M:ℚ)) :=
    OnRationalLattice.add dvd_rfl (by simpa only [Int.cast_natCast] using OnRationalLattice.intCast q.den (M:ℤ))
  have hnum : ((2*M:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (by decide : 0<2) hM).ne'
  have hinv : OnRationalLattice (2*M) (((2*M:ℕ):ℚ)⁻¹) := by
    unfold OnRationalLattice
    rw [Rat.den_inv_of_ne_zero hnum,Rat.num_natCast,Int.natAbs_natCast]
  have hmul:=OnRationalLattice.mul hsum hinv
  have hlat : OnRationalLattice (q.den*(2*M)) (normalized M q) := by
    simpa only [normalized,div_eq_mul_inv,Nat.cast_mul,Nat.cast_ofNat] using hmul
  exact Nat.le_of_dvd (Nat.mul_pos q.den_pos (Nat.mul_pos (by decide) hM)) hlat

theorem normalized_between (M : ℕ) (hM : 0<M) (q : ℚ) (h : -(M:ℚ)≤q ∧ q≤(M:ℚ)) :
    0≤normalized M q ∧ normalized M q≤1 := by
  have hMq : (0:ℚ)<M := by exact_mod_cast hM
  unfold normalized
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_one (by positivity : (0:ℚ)<2*(M:ℚ))).mpr
    linarith

theorem contains_closed (M k t : ℕ) (node : Interval) (hM : 0<M) (hcell : Cell M k t node)
    (q : ℚ) (hq : node.lo≤q ∧ q≤node.hi) :
    GeneralPaperProxyCell.Closed (2^k) t (normalized M q) := by
  have hden : (0:ℚ)<2*(M:ℚ) := by exact_mod_cast (Nat.mul_pos (by decide : 0<2) hM)
  have hlo : normalized M node.lo≤normalized M q := div_le_div_of_nonneg_right (by linarith only [hq.1]) hden.le
  have hhi : normalized M q≤normalized M node.hi := div_le_div_of_nonneg_right (by linarith only [hq.2]) hden.le
  rw [(normalized_cell M k t node hM hcell).1] at hlo
  rw [(normalized_cell M k t node hM hcell).2] at hhi
  simpa only [GeneralPaperProxyCell.Closed,GeneralPaperBucketGeometry.lower,GeneralPaperBucketGeometry.upper,
    Nat.cast_pow,Nat.cast_ofNat] using And.intro hlo hhi

end Blotto.PlayerSpecificNormalizedRoots
