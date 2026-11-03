import Blotto.RationalBinaryScale

/-! Actual significant-bit downward rounding selects the exact binary scale
and bounds its integer mantissa. Positivity/relative error do not need a caller
scale promise. Binary-exponent storage and primitive prices remain separate. -/

namespace Blotto
namespace SparseMW

def selectedExponent (x : ℚ) : ℤ :=
  let candidate := scaleCandidate x
  if candidateScale x ≤ x then candidate else candidate - 1

theorem binaryScale_eq_power (x : ℚ) : binaryScale x = (2 : ℚ) ^ selectedExponent x := by
  unfold binaryScale selectedExponent
  dsimp only
  split
  · rfl
  · rw [zpow_sub₀ (by norm_num), zpow_one]
    rfl

def roundDown (x : ℚ) (bits : ℕ) : ℚ := significandRoundAtScale x (binaryScale x) bits

def roundMantissa (x : ℚ) (bits : ℕ) : ℤ := Int.floor (x / (binaryScale x / (2 : ℚ) ^ bits))

theorem roundDown_certificate (x : ℚ) (hx : 0 < x) (bits : ℕ) :
    0 < roundDown x bits ∧ roundDown x bits ≤ x ∧ x < (1 + 1 / (2 : ℚ) ^ bits) * roundDown x bits :=
  significandRoundAtScale_certificate x (binaryScale x) bits (binaryScale_bounds x hx).1 (binaryScale_bounds x hx).2.1

theorem roundMantissa_bounds (x : ℚ) (hx : 0 < x) (bits : ℕ) :
    (2 : ℤ) ^ bits ≤ roundMantissa x bits ∧ roundMantissa x bits < (2 : ℤ) ^ (bits + 1) := by
  have hs := binaryScale_bounds x hx
  have hp : (0 : ℚ) < (2 : ℚ) ^ bits := by positivity
  have hu : 0 < binaryScale x / (2 : ℚ) ^ bits := div_pos hs.1 hp
  have hLow : (2 : ℚ) ^ bits ≤ x / (binaryScale x / (2 : ℚ) ^ bits) := by
    apply (le_div_iff₀ hu).mpr
    have he : (2 : ℚ) ^ bits * (binaryScale x / (2 : ℚ) ^ bits) = binaryScale x := by field_simp
    rw [he]
    exact hs.2.1
  have hHigh : x / (binaryScale x / (2 : ℚ) ^ bits) < (2 : ℚ) ^ (bits + 1) := by
    apply (div_lt_iff₀ hu).mpr
    rw [pow_succ]
    have he : ((2 : ℚ) ^ bits * 2) * (binaryScale x / (2 : ℚ) ^ bits) = 2 * binaryScale x := by field_simp
    rw [he]
    exact hs.2.2
  constructor
  · exact Int.le_floor.mpr (by exact_mod_cast hLow)
  · exact Int.floor_lt.mpr (by exact_mod_cast hHigh)

theorem roundDown_mantissa (x : ℚ) (bits : ℕ) :
    roundDown x bits = (roundMantissa x bits : ℚ) * (2 : ℚ) ^ (selectedExponent x - bits) := by
  unfold roundDown significandRoundAtScale gridRound roundMantissa
  rw [binaryScale_eq_power, zpow_sub₀ (by norm_num), zpow_natCast]

theorem roundMantissa_wordWidth (x : ℚ) (hx : 0 < x) (bits : ℕ) :
    binaryWordWidth (roundMantissa x bits).toNat ≤ bits + 1 := by
  have hb := roundMantissa_bounds x hx bits
  have hp : 0 < roundMantissa x bits := lt_of_lt_of_le (by positivity) hb.1
  have hCast : ((roundMantissa x bits).toNat : ℤ) = roundMantissa x bits := Int.toNat_of_nonneg hp.le
  have hHigh : (roundMantissa x bits).toNat < 2 ^ (bits + 1) := by
    have he : ((roundMantissa x bits).toNat : ℤ) < (2 : ℤ) ^ (bits + 1) := by rw [hCast]; exact hb.2
    exact_mod_cast he
  have hPos : (roundMantissa x bits).toNat ≠ 0 := by
    intro hzero
    rw [hzero] at hCast
    have hz : roundMantissa x bits = 0 := by simpa using hCast.symm
    exact (ne_of_gt hp) hz
  have hlog := (Nat.log2_lt hPos).mpr hHigh
  unfold binaryWordWidth
  omega

end SparseMW
end Blotto
