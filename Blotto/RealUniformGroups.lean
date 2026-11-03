import Blotto.RealGroupInputs
import Blotto.SmallGroupLaws

/-! Exact execution for two or three uniform groups, with every-path
budgets and equality to the retained grouped law. -/

namespace Blotto.UniformGroupSpec
open MeasureTheory

noncomputable def realSample {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (seed : RealFourSeed) : Allocation m := by
  by_cases h2 : m = 2
  · subst m
    exact complementaryPairPoint i.B (realGroupUnit seed)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.threeInput.realSample (realGroupThreeSeed seed)

theorem realSample_measurable {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    Measurable (i.realSample hm) := by
  rcases hm with rfl | rfl
  · exact (measurable_complementaryPairPoint i.B).comp realGroupUnit_measurable
  · exact i.threeInput.realSample_measurable.comp realGroupThreeSeed_measurable

theorem realSample_law {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    Measure.map (i.realSample hm) (FourInput.realInputLaw : Measure RealFourSeed) =
      (i.law hm : Measure (Allocation m)) := by
  rcases hm with rfl | rfl
  · change Measure.map (complementaryPairPoint i.B ∘ realGroupUnit) _ = _
    rw [← Measure.map_map (measurable_complementaryPairPoint i.B) realGroupUnit_measurable, realGroupUnit_law]
    rfl
  · change Measure.map (i.threeInput.realSample ∘ realGroupThreeSeed) _ = _
    rw [← Measure.map_map i.threeInput.realSample_measurable realGroupThreeSeed_measurable,
      realGroupThreeSeed_law, i.threeInput.realSample_law]
    rfl

theorem realSample_fullBudget {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (seed : RealFourSeed) (h : realGroupSeedValid seed) : FullBudget i.B (i.realSample hm seed) := by
  rcases hm with rfl | rfl
  · exact complementaryPairPoint_fullBudget i.B_pos.le (h.1 0)
  · exact i.threeInput.realSample_fullBudget _ (realGroupThreeSeed_bounds seed h 0)

end Blotto.UniformGroupSpec
