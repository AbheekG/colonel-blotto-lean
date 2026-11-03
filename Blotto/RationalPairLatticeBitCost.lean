import Blotto.RationalPairProgramBitCost
import Blotto.SignedLatticeSize

/-! Sharp shared-lattice register widths for the actual pair program. Every
pre-division register retains D; the probability's reduced words are bounded
by D as well. No reciprocal minimum gap enters the primitive price. -/

namespace Blotto.RationalPairProgram

theorem probability_wordWidth_lattice (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D)
    (h : p.Lattice D) (hi : p.lengthI ≤ 1) :
    rationalWordWidth p.probability ≤ 1 + 2 * binaryWordWidth D := by
  have hNum := p.words_num_le hD h hi
  have hDen := p.words_den_le hD h hi
  change p.probability.num.toNat ≤ D at hNum
  change p.probability.den ≤ D at hDen
  have hAbs : p.probability.num.natAbs = p.probability.num.toNat := by
    have he : (p.probability.num.natAbs : ℤ) = (p.probability.num.toNat : ℤ) :=
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr p.probability_bounds.1.le)).trans
        (Int.toNat_of_nonneg (Rat.num_nonneg.mpr p.probability_bounds.1.le)).symm
    exact_mod_cast he
  have hn := binaryWordWidth_mono hNum
  have hd := binaryWordWidth_mono hDen
  unfold rationalWordWidth
  rw [hAbs]
  omega

theorem final_wordBounds_lattice (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D)
    (h : p.Lattice D) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) :
    RationalArithmeticProgram.WordBounds (run p) (3 + 2 * binaryWordWidth D) := by
  have hUnit : ∀ q : ℚ, OnRationalLattice D q → (0 ≤ q ∧ q ≤ 1) →
      rationalWordWidth q ≤ 3 + 2 * binaryWordWidth D := by
    intro q hq hBox
    have hw := rationalWordWidth_lattice_bound hD hq hBox
    omega
  have hLI := hUnit p.lengthI h.lengthI ⟨p.interiorI.1.le.trans p.interiorI.2.le, hi⟩
  have hLJ := hUnit p.lengthJ h.lengthJ ⟨p.interiorJ.1.le.trans p.interiorJ.2.le, hj⟩
  have hRI := hUnit p.resourceI h.resourceI ⟨p.interiorI.1.le, p.interiorI.2.le.trans hi⟩
  have hRJ := hUnit p.resourceJ h.resourceJ ⟨p.interiorJ.1.le, p.interiorJ.2.le.trans hj⟩
  have hZero : rationalWordWidth (0 : ℚ) ≤ 3 + 2 * binaryWordWidth D := by
    have he : rationalWordWidth (0 : ℚ) = 3 := by decide
    omega
  have hTotal := p.total_wordWidth hD h hi hj
  have hDifference := p.lower_difference_wordWidth hD h hi hj
  have hLowerBox := p.branch_feasible (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)
  have hUpperBox := p.branch_feasible (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper)
  have hLower := hUnit p.lower (p.lower_on_lattice h.resourceI h.resourceJ h.lengthJ)
    ⟨hLowerBox.1, hLowerBox.2.1.trans hi⟩
  have hUpper := hUnit p.upper (p.upper_on_lattice h.resourceI h.resourceJ h.lengthI)
    ⟨hUpperBox.1, hUpperBox.2.1.trans hi⟩
  have hChoiceBox : 0 ≤ p.resourceI - p.lower ∧ p.resourceI - p.lower ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr p.lower_lt_resource.le
    · linarith [p.interiorI.2, hLowerBox.1]
  have hGapBox : 0 ≤ p.upper - p.lower ∧ p.upper - p.lower ≤ 1 := by
    constructor
    · exact p.gap_pos.le
    · linarith [hUpperBox.2.1, hLowerBox.1]
  have hChoice := hUnit (p.resourceI - p.lower) (p.choice_on_lattice h) hChoiceBox
  have hGap := hUnit (p.upper - p.lower) (p.gap_on_lattice h) hGapBox
  have hProbability := probability_wordWidth_lattice p hD h hi
  have hFin : ∀ j : Fin 12, rationalWordWidth ((run p).getD j.val 0) ≤ 3 + 2 * binaryWordWidth D := by
    intro j
    fin_cases j <;> rw [run_eq]
    · exact hLI
    · exact hLJ
    · exact hRI
    · exact hRJ
    · exact hZero
    · exact hTotal
    · change rationalWordWidth (p.total - p.lengthJ) ≤ 3 + 2 * binaryWordWidth D
      omega
    · exact hLower
    · exact hUpper
    · exact hChoice
    · exact hGap
    · change rationalWordWidth p.probability ≤ 3 + 2 * binaryWordWidth D
      omega
  intro j
  by_cases hIndex : j < 12
  · exact hFin ⟨j, hIndex⟩
  · have hIndex' : ¬j < (run p).size := by rw [run_size]; exact hIndex
    simpa only [Array.getD_eq_getD_getElem?, getElem?_neg (run p) j hIndex', Option.getD_none] using hZero

theorem prefix_wordBounds_lattice (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D)
    (h : p.Lattice D) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) (k : ℕ) :
    RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run (RealPairProgram.code.take k) (inputs p)) (3 + 2 * binaryWordWidth D) := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  exact (final_wordBounds_lattice p hD h hi hj).prefix (by omega) k

theorem preparationBitCost_lattice_sharp (model : RationalCostModel) (p : RationalRoundingPair)
    {D : ℕ} (hD : 0 < D) (h : p.Lattice D) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) :
    preparationBitCost model p ≤ 96 * model.rat (3 + 2 * binaryWordWidth D) := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  exact preparationBitCost_bound_of_final model p _ (by omega) (final_wordBounds_lattice p hD h hi hj)

end Blotto.RationalPairProgram
