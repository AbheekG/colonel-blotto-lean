import Blotto.SignificandPrecision

/-! The chosen dyadic exponent has magnitude bounded by input bit lengths,
and tolerance precision is bounded by its denominator's binary width. These
are encoding bounds, not a physical bit-time implementation certificate. -/

namespace Blotto
namespace SparseMW

theorem scaleCandidate_abs (x : ℚ) :
    (scaleCandidate x).natAbs ≤ binaryWordWidth x.num.toNat + binaryWordWidth x.den := by
  have h : |(x.num.toNat.log2 : ℤ) - (x.den.log2 : ℤ)| ≤
      (x.num.toNat.log2 : ℤ) + (x.den.log2 : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hn : (scaleCandidate x).natAbs ≤ x.num.toNat.log2 + x.den.log2 := by
    have he : ((scaleCandidate x).natAbs : ℤ) ≤ (x.num.toNat.log2 + x.den.log2 : ℕ) := by
      rw [Int.natCast_natAbs]
      simpa only [scaleCandidate, Nat.cast_add] using h
    exact_mod_cast he
  unfold binaryWordWidth
  omega

theorem selectedExponent_abs (x : ℚ) :
    (selectedExponent x).natAbs ≤ binaryWordWidth x.num.toNat + binaryWordWidth x.den + 1 := by
  have h := scaleCandidate_abs x
  unfold selectedExponent
  dsimp only
  split
  · omega
  · have he := Int.natAbs_sub_le (scaleCandidate x) 1
    norm_num at he
    omega

theorem roundingPrecision_bound (theta : ℚ) (ht : 0 < theta) :
    roundingPrecision theta ≤ binaryWordWidth theta.den := by
  have hn : 0 < theta.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr ht)
  have hp := lt_pow_binaryWordWidth theta.den
  apply binaryRatioPrecision_minimal theta.den theta.num.toNat hn
  have hmul : 2 ^ binaryWordWidth theta.den ≤ theta.num.toNat * 2 ^ binaryWordWidth theta.den :=
    Nat.le_mul_of_pos_left _ hn
  exact (Nat.le_of_lt hp).trans hmul

end SparseMW
end Blotto
