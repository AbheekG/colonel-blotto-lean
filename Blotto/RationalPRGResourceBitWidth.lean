import Blotto.BinaryWordWidth
import Blotto.RationalPRGResourceWords
import Blotto.RationalRoundingLatticeWords

/-! Resource words have bit width linear in the total normalized input word
width, independently of the rounding depth. This is an operand-size theorem;
portable binary serialization and complete primitive costs are separate. -/

namespace Blotto
open scoped BigOperators

theorem rationalWordWidth_lattice_bound {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hq : OnRationalLattice D q) (h : 0 ≤ q ∧ q ≤ 1) : rationalWordWidth q ≤ 1 + 2 * binaryWordWidth D := by
  have hn : q.num.natAbs = q.num.toNat := by
    have he : (q.num.natAbs : ℤ) = (q.num.toNat : ℤ) :=
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr h.1)).trans (Int.toNat_of_nonneg (Rat.num_nonneg.mpr h.1)).symm
    exact_mod_cast he
  have hwN := binaryWordWidth_mono (rationalLattice_reduced_numerator_le hD hq h)
  have hwD := binaryWordWidth_mono (rationalLattice_den_le hD hq)
  unfold rationalWordWidth
  rw [hn]
  omega

namespace RationalPRGInput

def inputWordWidth {n : ℕ} (i : RationalPRGInput n) : ℕ := rationalWordWidth i.b + ∑ j, rationalWordWidth (i.values j)

theorem valueDenominator_wordWidth {n : ℕ} (i : RationalPRGInput n) :
    binaryWordWidth i.valueDenominator ≤ 1 + ∑ j, binaryWordWidth (i.values j).den :=
  binaryWordWidth_finset_prod _ _

theorem latticeDenominator_wordWidth {n : ℕ} (i : RationalPRGInput n) :
    binaryWordWidth i.latticeDenominator ≤ 1 + i.inputWordWidth := by
  have hp := binaryWordWidth_mul i.b.den i.valueDenominator
  have hv := i.valueDenominator_wordWidth
  have hs : (∑ j, binaryWordWidth (i.values j).den) ≤ ∑ j, rationalWordWidth (i.values j) := by
    apply Finset.sum_le_sum
    intro j _
    unfold rationalWordWidth
    omega
  have hb : binaryWordWidth i.b.den ≤ rationalWordWidth i.b := by unfold rationalWordWidth; omega
  unfold latticeDenominator inputWordWidth
  omega

theorem resource_operand_wordWidth {n : ℕ} (i : RationalPRGInput n) (result : RationalActiveResources i.lengths)
    (hD : result.resource.OnLattice i.latticeDenominator)
    (hbox : InBox (fun j => (i.lengths j : ℝ)) result.resource.realAllocation) (j : Fin n) :
    rationalWordWidth (result.resource.allocation j) ≤ 3 + 2 * i.inputWordWidth := by
  have hb := hbox j
  change (0 : ℝ) ≤ (result.resource.allocation j : ℝ) ∧ (result.resource.allocation j : ℝ) ≤ (i.lengths j : ℝ) at hb
  have hbQ : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ i.lengths j := by exact_mod_cast hb
  have h1 : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ 1 :=
    ⟨hbQ.1, hbQ.2.trans ((i.small_fields j).trans i.b_le)⟩
  have hw := rationalWordWidth_lattice_bound i.latticeDenominator_pos (hD j) h1
  have hd := i.latticeDenominator_wordWidth
  omega

end RationalPRGInput
end Blotto
