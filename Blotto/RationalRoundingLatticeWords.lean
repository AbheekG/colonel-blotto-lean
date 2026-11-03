import Blotto.RationalResourceLattice

/-! Resource coin probabilities are ratios of two integer lattice differences.
An unreduced integer-word representation has the same probability and bounded
words. The maintained reduced words inherit these bounds as well. -/

namespace Blotto.RationalRoundingPair

structure Lattice (p : RationalRoundingPair) (D : ℕ) : Prop where
  lengthI : OnRationalLattice D p.lengthI
  lengthJ : OnRationalLattice D p.lengthJ
  resourceI : OnRationalLattice D p.resourceI
  resourceJ : OnRationalLattice D p.resourceJ

theorem lower_lt_resource (p : RationalRoundingPair) : p.lower < p.resourceI := by
  unfold lower
  apply max_lt p.interiorI.1
  dsimp [total]
  linarith [p.interiorJ.2]

theorem resource_lt_upper (p : RationalRoundingPair) : p.resourceI < p.upper := by
  unfold upper
  apply lt_min p.interiorI.2
  dsimp [total]
  linarith [p.interiorJ.1]

theorem gap_pos (p : RationalRoundingPair) : 0 < p.upper - p.lower := by
  linarith [p.lower_lt_resource, p.resource_lt_upper]

def choiceWord (p : RationalRoundingPair) (D : ℕ) : ℤ := latticeNumerator D (p.resourceI - p.lower)
def gapWord (p : RationalRoundingPair) (D : ℕ) : ℤ := latticeNumerator D (p.upper - p.lower)

theorem choice_on_lattice (p : RationalRoundingPair) {D : ℕ} (h : p.Lattice D) :
    OnRationalLattice D (p.resourceI - p.lower) :=
  h.resourceI.sub (p.lower_on_lattice h.resourceI h.resourceJ h.lengthJ)

theorem gap_on_lattice (p : RationalRoundingPair) {D : ℕ} (h : p.Lattice D) :
    OnRationalLattice D (p.upper - p.lower) :=
  (p.upper_on_lattice h.resourceI h.resourceJ h.lengthI).sub (p.lower_on_lattice h.resourceI h.resourceJ h.lengthJ)

theorem choiceWord_cast (p : RationalRoundingPair) {D : ℕ} (h : p.Lattice D) :
    (p.choiceWord D : ℚ) = (p.resourceI - p.lower) * (D : ℚ) := latticeNumerator_cast_eq_mul (p.choice_on_lattice h)

theorem gapWord_cast (p : RationalRoundingPair) {D : ℕ} (h : p.Lattice D) :
    (p.gapWord D : ℚ) = (p.upper - p.lower) * (D : ℚ) := latticeNumerator_cast_eq_mul (p.gap_on_lattice h)

theorem gapWord_pos (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) : 0 < p.gapWord D := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have he : (0 : ℚ) < (p.gapWord D : ℚ) := by rw [p.gapWord_cast h]; exact mul_pos p.gap_pos hd
  exact_mod_cast he

theorem choiceWord_bounds (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) :
    0 ≤ p.choiceWord D ∧ p.choiceWord D ≤ p.gapWord D := by
  have hd : (0 : ℚ) ≤ D := by exact_mod_cast le_of_lt hD
  have he : (0 : ℚ) ≤ (p.choiceWord D : ℚ) ∧ (p.choiceWord D : ℚ) ≤ (p.gapWord D : ℚ) := by
    rw [p.choiceWord_cast h, p.gapWord_cast h]
    exact ⟨mul_nonneg (by linarith [p.lower_lt_resource]) hd,
      mul_le_mul_of_nonneg_right (by linarith [p.resource_lt_upper]) hd⟩
  exact_mod_cast he

def latticeWords (p : RationalRoundingPair) (D : ℕ) (hD : 0 < D) (h : p.Lattice D) : ProbabilityWords where
  numerator := (p.choiceWord D).toNat
  denominator := (p.gapWord D).toNat
  denominator_pos := Int.pos_iff_toNat_pos.mp (p.gapWord_pos hD h)
  normalized := Int.toNat_le_toNat (p.choiceWord_bounds hD h).2

theorem probability_word_ratio (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) :
    p.probability = (p.choiceWord D : ℚ) / (p.gapWord D : ℚ) := by
  rw [p.choiceWord_cast h, p.gapWord_cast h]
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hg : p.upper - p.lower ≠ 0 := ne_of_gt p.gap_pos
  unfold probability
  field_simp

theorem latticeWords_rational (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) :
    (p.latticeWords D hD h).rational = p.probability := by
  change ((p.choiceWord D).toNat : ℚ) / ((p.gapWord D).toNat : ℚ) = p.probability
  have hn : ((p.choiceWord D).toNat : ℚ) = (p.choiceWord D : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (p.choiceWord_bounds hD h).1
  have hm : ((p.gapWord D).toNat : ℚ) = (p.gapWord D : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt (p.gapWord_pos hD h))
  rw [hn, hm]
  exact (p.probability_word_ratio hD h).symm

theorem gapWord_le (p : RationalRoundingPair) {D : ℕ} (h : p.Lattice D) (hI : p.lengthI ≤ 1) : p.gapWord D ≤ (D : ℤ) := by
  have hgap : 0 ≤ p.upper - p.lower ∧ p.upper - p.lower ≤ 1 := by
    have hu : p.upper ≤ p.lengthI := min_le_left _ _
    have hl : 0 ≤ p.lower := le_max_left _ _
    exact ⟨le_of_lt p.gap_pos, by linarith⟩
  exact (latticeNumerator_bounds (p.gap_on_lattice h) hgap).2

theorem latticeWords_den_le (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) (hI : p.lengthI ≤ 1) :
    (p.latticeWords D hD h).denominator ≤ D := by
  have he := Int.toNat_le_toNat (p.gapWord_le h hI)
  exact he

theorem words_den_le (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) (hI : p.lengthI ≤ 1) :
    p.words.denominator ≤ D := by
  have he : p.probability = Rat.divInt (p.choiceWord D) (p.gapWord D) := by
    rw [Rat.divInt_eq_div]
    exact p.probability_word_ratio hD h
  have hd : (p.probability.den : ℤ) ∣ p.gapWord D := by rw [he]; exact Rat.den_dvd _ _
  rcases hd with ⟨k, hk⟩
  have hp : (0 : ℤ) < p.probability.den := by exact_mod_cast p.probability.den_pos
  have hm := p.gapWord_pos hD h
  have hkp : 0 < k := by nlinarith
  have hk1 : 1 ≤ k := by omega
  have hden : (p.probability.den : ℤ) ≤ p.gapWord D := by nlinarith
  have hbound : (p.probability.den : ℤ) ≤ (D : ℤ) := hden.trans (p.gapWord_le h hI)
  exact_mod_cast hbound

theorem words_num_le (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D) (hI : p.lengthI ≤ 1) :
    p.words.numerator ≤ D := p.words.normalized.trans (p.words_den_le hD h hI)

end Blotto.RationalRoundingPair
