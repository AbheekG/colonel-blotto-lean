import Blotto.RationalPRGResourceBitWidth

/-! Signed arithmetic intermediates on the resource lattice. Bounds use
absolute numerators, so pre-clipping negative differences are included. -/

namespace Blotto

theorem rationalLattice_abs_numerator_le {D M : ℕ} (hD : 0 < D) {q : ℚ}
    (hq : OnRationalLattice D q) (ha : |q| ≤ (M : ℚ)) : q.num.natAbs ≤ M * D := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hrep : |(q.num : ℚ)| / (q.den : ℚ) = |q| := by
    have he := congrArg abs q.num_div_den
    simpa only [abs_div, abs_of_pos hd] using he
  have he : (q.num.natAbs : ℚ) ≤ (M : ℚ) * q.den := by
    rw [Nat.cast_natAbs]
    push_cast
    apply (div_le_iff₀ hd).mp
    rw [hrep]
    exact ha
  have hn : q.num.natAbs ≤ M * q.den := by exact_mod_cast he
  exact hn.trans (Nat.mul_le_mul_left M (rationalLattice_den_le hD hq))

theorem rationalWordWidth_abs_lattice_bound {D M : ℕ} (hD : 0 < D) {q : ℚ}
    (hq : OnRationalLattice D q) (ha : |q| ≤ (M : ℚ)) :
    rationalWordWidth q ≤ 1 + binaryWordWidth M + 2 * binaryWordWidth D := by
  have hn := binaryWordWidth_mono (rationalLattice_abs_numerator_le hD hq ha)
  have hm := binaryWordWidth_mul M D
  have hd := binaryWordWidth_mono (rationalLattice_den_le hD hq)
  unfold rationalWordWidth
  omega

namespace RationalRoundingPair

theorem total_abs_le (p : RationalRoundingPair) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) : |p.total| ≤ 2 := by
  have h0 : 0 ≤ p.total := by dsimp [total]; linarith [p.interiorI.1, p.interiorJ.1]
  rw [abs_of_nonneg h0]
  dsimp [total]
  linarith [p.interiorI.2, p.interiorJ.2]

theorem lower_difference_abs_le (p : RationalRoundingPair) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) :
    |p.total - p.lengthJ| ≤ 1 := by
  apply abs_le.mpr
  dsimp [total]
  constructor <;> linarith [p.interiorI.1, p.interiorJ.1, p.interiorI.2, p.interiorJ.2]

theorem total_wordWidth (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D)
    (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) : rationalWordWidth p.total ≤ 3 + 2 * binaryWordWidth D := by
  have he := rationalWordWidth_abs_lattice_bound (M := 2) hD (p.total_on_lattice h.resourceI h.resourceJ) (p.total_abs_le hi hj)
  have htwo : binaryWordWidth 2 = 2 := by decide
  rw [htwo] at he
  exact he

theorem lower_difference_wordWidth (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D)
    (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) : rationalWordWidth (p.total - p.lengthJ) ≤ 2 + 2 * binaryWordWidth D := by
  have he := rationalWordWidth_abs_lattice_bound (M := 1) hD
    ((p.total_on_lattice h.resourceI h.resourceJ).sub h.lengthJ) (p.lower_difference_abs_le hi hj)
  have hone : binaryWordWidth 1 = 1 := by decide
  rw [hone] at he
  exact he

end RationalRoundingPair
end Blotto
