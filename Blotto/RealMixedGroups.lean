import Blotto.RealGroupInputs
import Blotto.SmallGroupLaws

/-! Exact two/three uniform-group execution with one fractional coordinate. -/

namespace Blotto.MixedGroupSpec
open MeasureTheory

noncomputable def realSample {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (seed : RealFourSeed) : Allocation (m + 1) := by
  by_cases h2 : m = 2
  · subst m
    exact i.threeInput.realSample (realGroupThreeSeed seed)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.realSample seed

theorem realSample_measurable {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) :
    Measurable (i.realSample hm) := by
  rcases hm with rfl | rfl
  · exact i.threeInput.realSample_measurable.comp realGroupThreeSeed_measurable
  · exact i.fourInput.realSample_measurable

theorem realSample_law {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) :
    Measure.map (i.realSample hm) (FourInput.realInputLaw : Measure RealFourSeed) =
      (i.law hm : Measure (Allocation (m + 1))) := by
  rcases hm with rfl | rfl
  · change Measure.map (i.threeInput.realSample ∘ realGroupThreeSeed) _ = _
    rw [← Measure.map_map i.threeInput.realSample_measurable realGroupThreeSeed_measurable,
      realGroupThreeSeed_law, i.threeInput.realSample_law]
    rfl
  · exact i.fourInput.realSample_law

theorem realSample_fullBudget {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (seed : RealFourSeed) (h : realGroupSeedValid seed) : FullBudget i.B (i.realSample hm seed) := by
  rcases hm with rfl | rfl
  · exact i.threeInput.realSample_fullBudget _ (realGroupThreeSeed_bounds seed h 0)
  · exact i.fourInput.realSample_fullBudget seed (h.1 0) h.2

end Blotto.MixedGroupSpec
