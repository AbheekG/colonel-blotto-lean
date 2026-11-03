import Blotto.RealPRGSampler
import Blotto.RationalPRGOriginalInput

/-! Exact-real allocation arrays scale back to the original ordered rational
budgets. The full continuous security domain and tie rule are preserved by
the existing positive-scaling theorem. -/

namespace Blotto.RationalPRGOriginalInput
open MeasureTheory

noncomputable def realRichArray {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) : FixedArrayTable n ℝ :=
  let base := i.normalizedInput.real.realRichArray seed
  FixedArrayTable.ofFn fun j => (i.a : ℝ) * base.read j

noncomputable def realPoorArray {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) : FixedArrayTable n ℝ :=
  let base := i.normalizedInput.real.realPoorArray seed
  FixedArrayTable.ofFn fun j => (i.a : ℝ) * base.read j

noncomputable def realRichSample {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) : Allocation n :=
  (i.realRichArray seed).read

noncomputable def realPoorSample {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) : Allocation n :=
  (i.realPoorArray seed).read

theorem realRichSample_scale {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) :
    i.realRichSample seed = scaleAllocation (i.a : ℝ) (i.normalizedInput.real.realRichSample seed) := by
  funext j
  simp only [realRichSample, realRichArray, FixedArrayTable.read_ofFn, scaleAllocation]
  rfl

theorem realPoorSample_scale {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n) :
    i.realPoorSample seed = scaleAllocation (i.a : ℝ) (i.normalizedInput.real.realPoorSample seed) := by
  funext j
  simp only [realPoorSample, realPoorArray, FixedArrayTable.read_ofFn, scaleAllocation]
  rfl

theorem realRichSample_measurable {n : ℕ} (i : RationalPRGOriginalInput n) : Measurable i.realRichSample := by
  have hEq : i.realRichSample = scaleAllocation (i.a : ℝ) ∘ i.normalizedInput.real.realRichSample := funext i.realRichSample_scale
  rw [hEq]
  exact (measurable_scaleAllocation _).comp i.normalizedInput.real.realRichSample_measurable

theorem realPoorSample_measurable {n : ℕ} (i : RationalPRGOriginalInput n) : Measurable i.realPoorSample := by
  have hEq : i.realPoorSample = scaleAllocation (i.a : ℝ) ∘ i.normalizedInput.real.realPoorSample := funext i.realPoorSample_scale
  rw [hEq]
  exact (measurable_scaleAllocation _).comp i.normalizedInput.real.realPoorSample_measurable

noncomputable def realRichLaw {n : ℕ} (i : RationalPRGOriginalInput n) : Mixed n :=
  scaleLaw (i.a : ℝ) i.normalizedInput.real.realRichLaw

noncomputable def realPoorLaw {n : ℕ} (i : RationalPRGOriginalInput n) : Mixed n :=
  scaleLaw (i.a : ℝ) i.normalizedInput.real.realPoorLaw

theorem realRichSample_law {n : ℕ} (i : RationalPRGOriginalInput n) :
    Measure.map i.realRichSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (i.realRichLaw : Measure (Allocation n)) := by
  have hEq : i.realRichSample = scaleAllocation (i.a : ℝ) ∘ i.normalizedInput.real.realRichSample := funext i.realRichSample_scale
  rw [hEq, ← Measure.map_map (measurable_scaleAllocation _) i.normalizedInput.real.realRichSample_measurable]
  rfl

theorem realPoorSample_law {n : ℕ} (i : RationalPRGOriginalInput n) :
    Measure.map i.realPoorSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (i.realPoorLaw : Measure (Allocation n)) := by
  have hEq : i.realPoorSample = scaleAllocation (i.a : ℝ) ∘ i.normalizedInput.real.realPoorSample := funext i.realPoorSample_scale
  rw [hEq, ← Measure.map_map (measurable_scaleAllocation _) i.normalizedInput.real.realPoorSample_measurable]
  rfl

theorem realRichSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n)
    (h : realGroupSeedValid seed.2) : FullBudget (i.a : ℝ) (i.realRichSample seed) := by
  have ha : (0 : ℝ) ≤ i.a := by exact_mod_cast i.a_pos.le
  rw [i.realRichSample_scale]
  simpa only [mul_one] using scaleAllocation_fullBudget ha (i.normalizedInput.real.realRichSample_fullBudget seed h)

theorem realPoorSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (seed : RealLottoSeed n)
    (h : realGroupSeedValid seed.2) : FullBudget (i.b : ℝ) (i.realPoorSample seed) := by
  have ha : (0 : ℝ) ≤ i.a := by exact_mod_cast i.a_pos.le
  have hDraw := scaleAllocation_fullBudget ha (i.normalizedInput.real.realPoorSample_fullBudget seed h)
  change FullBudget ((i.a : ℝ) * (i.normalizedInput.b : ℝ)) _ at hDraw
  rw [i.rescaled_poor_budget] at hDraw
  rw [i.realPoorSample_scale]
  exact hDraw

theorem realOutputs_product_law {n : ℕ} (i : RationalPRGOriginalInput n) :
    Measure.map (Prod.map i.realRichSample i.realPoorSample)
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.realRichLaw : Measure (Allocation n)).prod (i.realPoorLaw : Measure (Allocation n)) := by
  rw [← Measure.map_prod_map _ _ i.realRichSample_measurable i.realPoorSample_measurable,
    i.realRichSample_law, i.realPoorSample_law]

theorem realEquilibrium {n : ℕ} (i : RationalPRGOriginalInput n) :
    regret i.realValues (i.a : ℝ) i.realRichLaw i.realPoorLaw = 0 ∧
      regret i.realValues (i.b : ℝ) i.realPoorLaw i.realRichLaw = 0 ∧
      expected i.realValues i.realRichLaw i.realPoorLaw = 1 - (i.normalizedInput.b : ℝ) / 2 ∧
      expected i.realValues i.realPoorLaw i.realRichLaw = (i.normalizedInput.b : ℝ) / 2 := by
  have ha : (0 : ℝ) < i.a := by exact_mod_cast i.a_pos
  have hA := regret_scale i.realValues ha 1 i.normalizedInput.real.realRichLaw i.normalizedInput.real.realPoorLaw
  have hB := regret_scale i.realValues ha (i.normalizedInput.b : ℝ) i.normalizedInput.real.realPoorLaw i.normalizedInput.real.realRichLaw
  rw [mul_one] at hA
  rw [i.rescaled_poor_budget] at hB
  change regret i.realValues (i.a : ℝ) (scaleLaw (i.a : ℝ) _) (scaleLaw (i.a : ℝ) _) = 0 ∧
    regret i.realValues (i.b : ℝ) (scaleLaw (i.a : ℝ) _) (scaleLaw (i.a : ℝ) _) = 0 ∧
    expected i.realValues (scaleLaw (i.a : ℝ) _) (scaleLaw (i.a : ℝ) _) = _ ∧
    expected i.realValues (scaleLaw (i.a : ℝ) _) (scaleLaw (i.a : ℝ) _) = _
  rw [hA, hB, expected_scale i.realValues ha, expected_scale i.realValues ha, ← i.normalized_values]
  exact i.normalizedInput.real.realEquilibrium

end Blotto.RationalPRGOriginalInput
