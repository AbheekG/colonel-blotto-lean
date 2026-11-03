import Blotto.RationalPRGOriginalInput
import Blotto.RationalPRGResourceBitWidth

/-! Normalization's lattice bound is charged to original game words.
The richer budget numerator, not only its denominator, enters the normalized
ratio's denominator. All raw input words are counted once. -/

namespace Blotto.RationalPRGOriginalInput
open scoped BigOperators

def originalInputWordWidth {n : ℕ} (i : RationalPRGOriginalInput n) : ℕ :=
  rationalWordWidth i.a + rationalWordWidth i.b + ∑ j, rationalWordWidth (i.values j)

def originalLatticeDenominator {n : ℕ} (i : RationalPRGOriginalInput n) : ℕ :=
  i.b.den * i.a.num.natAbs * ∏ j, (i.values j).den

theorem originalLatticeDenominator_pos {n : ℕ} (i : RationalPRGOriginalInput n) : 0 < i.originalLatticeDenominator := by
  have ha : 0 < i.a.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr i.a_pos))
  exact Nat.mul_pos (Nat.mul_pos i.b.den_pos ha) (Finset.prod_pos (fun j _ => (i.values j).den_pos))

theorem normalized_ratio_den_dvd {n : ℕ} (i : RationalPRGOriginalInput n) :
    i.normalizedInput.b.den ∣ i.b.den * i.a.num.natAbs := by
  have ha : i.a.num ≠ 0 := ne_of_gt (Rat.num_pos.mpr i.a_pos)
  change (i.b / i.a).den ∣ i.b.den * i.a.num.natAbs
  simpa only [div_eq_mul_inv, Rat.den_inv, ite_eq_right ha] using Rat.mul_den_dvd i.b i.a⁻¹

theorem normalized_lattice_dvd_original {n : ℕ} (i : RationalPRGOriginalInput n) :
    i.normalizedInput.latticeDenominator ∣ i.originalLatticeDenominator :=
  Nat.mul_dvd_mul i.normalized_ratio_den_dvd (dvd_refl (∏ j, (i.values j).den))

theorem originalLatticeDenominator_wordWidth {n : ℕ} (i : RationalPRGOriginalInput n) :
    binaryWordWidth i.originalLatticeDenominator ≤ 1 + i.originalInputWordWidth := by
  have h1 := binaryWordWidth_mul (i.b.den * i.a.num.natAbs) (∏ j, (i.values j).den)
  have h2 := binaryWordWidth_mul i.b.den i.a.num.natAbs
  have hv := binaryWordWidth_finset_prod (fun j => (i.values j).den) Finset.univ
  have hs : (∑ j, binaryWordWidth (i.values j).den) ≤ ∑ j, rationalWordWidth (i.values j) := by
    apply Finset.sum_le_sum
    intro j _
    unfold rationalWordWidth
    omega
  have ha : binaryWordWidth i.a.num.natAbs ≤ rationalWordWidth i.a := by unfold rationalWordWidth; omega
  have hb : binaryWordWidth i.b.den ≤ rationalWordWidth i.b := by unfold rationalWordWidth; omega
  unfold originalLatticeDenominator originalInputWordWidth
  omega

theorem normalized_lattice_wordWidth_original {n : ℕ} (i : RationalPRGOriginalInput n) :
    binaryWordWidth i.normalizedInput.latticeDenominator ≤ 1 + i.originalInputWordWidth :=
  (binaryWordWidth_mono (Nat.le_of_dvd i.originalLatticeDenominator_pos i.normalized_lattice_dvd_original)).trans
    i.originalLatticeDenominator_wordWidth

theorem resource_operand_original_wordWidth {n : ℕ} (i : RationalPRGOriginalInput n)
    (result : RationalActiveResources i.normalizedInput.lengths)
    (hD : result.resource.OnLattice i.normalizedInput.latticeDenominator)
    (hbox : InBox (fun j => (i.normalizedInput.lengths j : ℝ)) result.resource.realAllocation) (j : Fin n) :
    rationalWordWidth (result.resource.allocation j) ≤ 3 + 2 * i.originalInputWordWidth := by
  have hb := hbox j
  change (0 : ℝ) ≤ (result.resource.allocation j : ℝ) ∧
    (result.resource.allocation j : ℝ) ≤ (i.normalizedInput.lengths j : ℝ) at hb
  have hbQ : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ i.normalizedInput.lengths j := by exact_mod_cast hb
  have h1 : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ 1 :=
    ⟨hbQ.1, hbQ.2.trans ((i.normalizedInput.small_fields j).trans i.normalizedInput.b_le)⟩
  have hw := rationalWordWidth_lattice_bound i.normalizedInput.latticeDenominator_pos (hD j) h1
  have hd := i.normalized_lattice_wordWidth_original
  omega

end Blotto.RationalPRGOriginalInput
