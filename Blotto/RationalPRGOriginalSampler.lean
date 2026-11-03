import Blotto.RationalPRGOriginalInput

/-! Native output scaling returns both whole allocation laws at their
original rational budgets, preserving all continuous regret guarantees. -/

namespace Blotto.RationalPRGOriginalInput
open MeasureTheory

def richSampleArray {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  let row := i.normalizedInput.richSample K bits
  RationalResourceArray.ofAllocation (fun j => i.a * row j)

def poorSampleArray {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  let row := i.normalizedInput.poorSample K bits
  RationalResourceArray.ofAllocation (fun j => i.a * row j)

def richSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  (i.richSampleArray K bits).allocation

def poorSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  (i.poorSampleArray K bits).allocation

theorem richSample_apply {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    i.richSample K bits j = i.a * i.normalizedInput.richSample K bits j := by
  simp [richSample, richSampleArray, RationalResourceArray.allocation_ofAllocation]

theorem poorSample_apply {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    i.poorSample K bits j = i.a * i.normalizedInput.poorSample K bits j := by
  simp [poorSample, poorSampleArray, RationalResourceArray.allocation_ofAllocation]

noncomputable def richSampleLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.richSample K bits j : ℝ))

noncomputable def poorSampleLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.poorSample K bits j : ℝ))

theorem richSampleLaw_eq_scale {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.richSampleLaw K = scaleLaw (i.a : ℝ) (i.normalizedInput.richSampleLaw K) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (i.richSample K bits j : ℝ))
    (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K) : Measure _) =
    Measure.map (scaleAllocation (i.a : ℝ)) (Measure.map (fun bits j => (i.normalizedInput.richSample K bits j : ℝ))
      (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K) : Measure _))
  rw [Measure.map_map (measurable_scaleAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits j
  simp only [i.richSample_apply, Rat.cast_mul, Function.comp_def, scaleAllocation]

theorem poorSampleLaw_eq_scale {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.poorSampleLaw K = scaleLaw (i.a : ℝ) (i.normalizedInput.poorSampleLaw K) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (i.poorSample K bits j : ℝ))
    (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K) : Measure _) =
    Measure.map (scaleAllocation (i.a : ℝ)) (Measure.map (fun bits j => (i.normalizedInput.poorSample K bits j : ℝ))
      (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K) : Measure _))
  rw [Measure.map_map (measurable_scaleAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits j
  simp only [i.poorSample_apply, Rat.cast_mul, Function.comp_def, scaleAllocation]

theorem richSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.a : ℝ) (fun j => (i.richSample K bits j : ℝ)) := by
  have ha : (0 : ℝ) ≤ i.a := by exact_mod_cast le_of_lt i.a_pos
  have h := scaleAllocation_fullBudget ha (i.normalizedInput.richSample_fullBudget K bits)
  have he : (fun j => (i.richSample K bits j : ℝ)) =
      scaleAllocation (i.a : ℝ) (fun j => (i.normalizedInput.richSample K bits j : ℝ)) := by
    funext j
    simp only [i.richSample_apply, scaleAllocation, Rat.cast_mul]
  rw [he]
  simpa only [mul_one] using h

theorem poorSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.b : ℝ) (fun j => (i.poorSample K bits j : ℝ)) := by
  have ha : (0 : ℝ) ≤ i.a := by exact_mod_cast le_of_lt i.a_pos
  have h := scaleAllocation_fullBudget ha (i.normalizedInput.poorSample_fullBudget K bits)
  rw [i.rescaled_poor_budget] at h
  have he : (fun j => (i.poorSample K bits j : ℝ)) =
      scaleAllocation (i.a : ℝ) (fun j => (i.normalizedInput.poorSample K bits j : ℝ)) := by
    funext j
    simp only [i.poorSample_apply, scaleAllocation, Rat.cast_mul]
  rw [he]
  exact h

theorem sample_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    regret i.realValues (i.a : ℝ) (i.richSampleLaw K) (i.poorSampleLaw K) ≤ 5 / (2 : ℝ) ^ K ∧
      regret i.realValues (i.b : ℝ) (i.poorSampleLaw K) (i.richSampleLaw K) ≤ 5 / (2 : ℝ) ^ K := by
  have ha : (0 : ℝ) < i.a := by exact_mod_cast i.a_pos
  have hA := regret_scale i.realValues ha 1 (i.normalizedInput.richSampleLaw K) (i.normalizedInput.poorSampleLaw K)
  have hB := regret_scale i.realValues ha (i.normalizedInput.b : ℝ)
    (i.normalizedInput.poorSampleLaw K) (i.normalizedInput.richSampleLaw K)
  rw [mul_one, ← i.richSampleLaw_eq_scale K, ← i.poorSampleLaw_eq_scale K] at hA
  rw [i.rescaled_poor_budget, ← i.richSampleLaw_eq_scale K, ← i.poorSampleLaw_eq_scale K] at hB
  rw [hA, hB, ← i.normalized_values]
  exact i.normalizedInput.sample_regrets K

theorem rational_accuracy_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (ε : ℚ) (hε : 0 < ε) :
    regret i.realValues (i.a : ℝ) (i.richSampleLaw (rationalAccuracyPrecision ε)) (i.poorSampleLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) ∧
      regret i.realValues (i.b : ℝ) (i.poorSampleLaw (rationalAccuracyPrecision ε)) (i.richSampleLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) := by
  have h := i.sample_regrets (rationalAccuracyPrecision ε)
  have he := prg_precision_error (by exact_mod_cast hε) (rationalAccuracyPrecision_real_guard ε hε)
  have hsum : 2 * (5 / (2 * (2 : ℝ) ^ rationalAccuracyPrecision ε)) = 5 / (2 : ℝ) ^ rationalAccuracyPrecision ε := by field_simp
  rw [hsum] at he
  constructor <;> linarith [h.1, h.2]

end Blotto.RationalPRGOriginalInput
