import Blotto.RationalLotteryTranslate
import Blotto.BinaryMixture

/-! Native constant-size descriptor assembly. Padding duplicates a feasible
endpoint pair with zero weight; binary assembly concatenates the two weighted
tables. Neither operation enumerates allocation support. -/

namespace Blotto.RationalSegmentLottery
open MeasureTheory
open scoped BigOperators

def padRight {n k : ℕ} (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k) : RationalSegmentLottery n (k + m) where
  weight := Fin.addCases l.weight (fun _ => 0)
  P := Fin.addCases l.P (fun _ => l.P fallback)
  Q := Fin.addCases l.Q (fun _ => l.Q fallback)
  nonnegative := by
    intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left] using l.nonnegative j
    · intro j; simp only [Fin.addCases_right]; exact le_rfl
  mass := by rw [Fin.sum_univ_add]; simp [l.mass]

def binary {n k m : ℕ} (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) : RationalSegmentLottery n (k + m) where
  weight := Fin.addCases (fun j => p * l.weight j) (fun j => (1 - p) * t.weight j)
  P := Fin.addCases l.P t.P
  Q := Fin.addCases l.Q t.Q
  nonnegative := by
    intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left] using mul_nonneg hp.1 (l.nonnegative j)
    · intro j; simpa only [Fin.addCases_right] using mul_nonneg (sub_nonneg.mpr hp.2) (t.nonnegative j)
  mass := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, ← Finset.mul_sum, l.mass, t.mass, mul_one]
    ring

theorem padRight_law {n k : ℕ} (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k) :
    (l.padRight m fallback).real.law = l.real.law := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.sum (fun slot => ENNReal.ofReal ((l.padRight m fallback).weight slot : ℝ) •
      (segmentLaw (fun j => ((l.padRight m fallback).P slot j : ℝ))
        (fun j => ((l.padRight m fallback).Q slot j : ℝ)) : Measure (Allocation n)))) =
    Measure.sum (fun slot => ENNReal.ofReal (l.weight slot : ℝ) •
      (segmentLaw (fun j => (l.P slot j : ℝ)) (fun j => (l.Q slot j : ℝ)) : Measure (Allocation n)))
  simp [padRight,
    Measure.sum_fintype, Fin.sum_univ_add]

theorem binary_law {n k m : ℕ} (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) :
    (binary p hp l t).real.law = binaryLaw (p : ℝ) (by exact_mod_cast hp) l.real.law t.real.law := by
  have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp.1
  have hqR : (0 : ℝ) ≤ 1 - (p : ℝ) := by exact_mod_cast sub_nonneg.mpr hp.2
  apply ProbabilityMeasure.toMeasure_injective
  rw [binaryLaw_measure]
  change (Measure.sum (fun slot => ENNReal.ofReal ((binary p hp l t).weight slot : ℝ) •
      (segmentLaw (fun j => ((binary p hp l t).P slot j : ℝ))
        (fun j => ((binary p hp l t).Q slot j : ℝ)) : Measure (Allocation n)))) =
    ENNReal.ofReal (p : ℝ) • Measure.sum (fun slot => ENNReal.ofReal (l.weight slot : ℝ) •
      (segmentLaw (fun j => (l.P slot j : ℝ)) (fun j => (l.Q slot j : ℝ)) : Measure (Allocation n))) +
    ENNReal.ofReal (1 - (p : ℝ)) • Measure.sum (fun slot => ENNReal.ofReal (t.weight slot : ℝ) •
      (segmentLaw (fun j => (t.P slot j : ℝ)) (fun j => (t.Q slot j : ℝ)) : Measure (Allocation n)))
  simp only [binary, Measure.sum_fintype,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  simp_rw [ENNReal.ofReal_mul hpR, ENNReal.ofReal_mul hqR, mul_smul]
  rw [Finset.smul_sum, Finset.smul_sum]

theorem padRight_endpoints {n k : ℕ} (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k)
    {B : ℝ} (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot)) :
    ∀ slot, FullBudget B ((l.padRight m fallback).real.P slot) ∧ FullBudget B ((l.padRight m fallback).real.Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j
    simpa only [padRight, real, Fin.addCases_left] using h j
  · intro j
    simpa only [padRight, real, Fin.addCases_right] using h fallback

theorem binary_endpoints {n k m : ℕ} (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) {B : ℝ}
    (hl : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot))
    (ht : ∀ slot, FullBudget B (t.real.P slot) ∧ FullBudget B (t.real.Q slot)) :
    ∀ slot, FullBudget B ((binary p hp l t).real.P slot) ∧ FullBudget B ((binary p hp l t).real.Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j
    simpa only [binary, real, Fin.addCases_left] using hl j
  · intro j
    simpa only [binary, real, Fin.addCases_right] using ht j

end Blotto.RationalSegmentLottery
