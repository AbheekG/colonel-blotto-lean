import Blotto.RealLottoSampler
import Blotto.PRGEquilibrium

/-! Actual exact-real PRG allocation arrays realize the constructed mixed
strategies. Independent player packets give their product law and the full
continuous-deviation equilibrium, including the canonical half-tie rule. -/

namespace Blotto.PRGInput
open MeasureTheory

noncomputable def realRichArray {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) : FixedArrayTable n ℝ :=
  i.richSystem.realSampleArray seed

noncomputable def realPoorArray {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) : FixedArrayTable n ℝ :=
  i.poorSystem.realSampleArray seed

noncomputable def realRichSample {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) : Allocation n :=
  (i.realRichArray seed).read

noncomputable def realPoorSample {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) : Allocation n :=
  (i.realPoorArray seed).read

theorem realRichSample_measurable {n : ℕ} (i : PRGInput n) : Measurable i.realRichSample := i.richSystem.realSample_measurable
theorem realPoorSample_measurable {n : ℕ} (i : PRGInput n) : Measurable i.realPoorSample := i.poorSystem.realSample_measurable

theorem realRichSample_law {n : ℕ} (i : PRGInput n) :
    Measure.map i.realRichSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (i.richLaw : Measure (Allocation n)) := i.richSystem.realSample_law

theorem realPoorSample_law {n : ℕ} (i : PRGInput n) :
    Measure.map i.realPoorSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (i.poorLaw : Measure (Allocation n)) := i.poorSystem.realSample_law

theorem realRichSample_fullBudget {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) (h : realGroupSeedValid seed.2) :
    FullBudget 1 (i.realRichSample seed) := i.richSystem.realSample_fullBudget seed h

theorem realPoorSample_fullBudget {n : ℕ} (i : PRGInput n) (seed : RealLottoSeed n) (h : realGroupSeedValid seed.2) :
    FullBudget i.b (i.realPoorSample seed) := i.poorSystem.realSample_fullBudget seed h

noncomputable def realRichLaw {n : ℕ} (i : PRGInput n) : Mixed n :=
  ⟨Measure.map i.realRichSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)), by
    rw [i.realRichSample_law]
    infer_instance⟩

noncomputable def realPoorLaw {n : ℕ} (i : PRGInput n) : Mixed n :=
  ⟨Measure.map i.realPoorSample (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)), by
    rw [i.realPoorSample_law]
    infer_instance⟩

theorem realRichLaw_eq {n : ℕ} (i : PRGInput n) : i.realRichLaw = i.richLaw :=
  ProbabilityMeasure.toMeasure_injective i.realRichSample_law

theorem realPoorLaw_eq {n : ℕ} (i : PRGInput n) : i.realPoorLaw = i.poorLaw :=
  ProbabilityMeasure.toMeasure_injective i.realPoorSample_law

theorem realOutputs_product_law {n : ℕ} (i : PRGInput n) :
    Measure.map (Prod.map i.realRichSample i.realPoorSample)
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.richLaw : Measure (Allocation n)).prod (i.poorLaw : Measure (Allocation n)) := by
  rw [← Measure.map_prod_map _ _ i.realRichSample_measurable i.realPoorSample_measurable,
    i.realRichSample_law, i.realPoorSample_law]

theorem realEquilibrium {n : ℕ} (i : PRGInput n) :
    regret i.values 1 i.realRichLaw i.realPoorLaw = 0 ∧
      regret i.values i.b i.realPoorLaw i.realRichLaw = 0 ∧
      expected i.values i.realRichLaw i.realPoorLaw = 1 - i.b / 2 ∧
      expected i.values i.realPoorLaw i.realRichLaw = i.b / 2 := by
  rw [i.realRichLaw_eq, i.realPoorLaw_eq]
  exact i.equilibrium

end Blotto.PRGInput
