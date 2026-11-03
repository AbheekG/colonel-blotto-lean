import Blotto.AveragedBitMixtures
import Blotto.ParameterLaw

/-! Finite fair averaging commutes with every measurable allocation map,
including sparse cached proportional output maps. -/

namespace Blotto
open MeasureTheory

theorem averaged_fairBit_map {n m : ℕ} (K : ℕ) (law : (Fin K → Bool) → Mixed n)
    (f : Allocation n → Allocation m) (hf : Measurable f) :
    averagedLaw (fairBitLaw K) (fun bits => (law bits).map f) (measurable_of_countable _) =
      (averagedLaw (fairBitLaw K) law (measurable_of_countable _)).map f := by
  apply ProbabilityMeasure.toMeasure_injective
  change (fairBitLaw K : Measure (Fin K → Bool)).bind
    (fun bits => Measure.map f (law bits : Measure (Allocation n))) =
    Measure.map f ((fairBitLaw K : Measure (Fin K → Bool)).bind (fun bits => (law bits : Measure (Allocation n))))
  exact (map_bind_family _ _ (measurable_of_countable _) f hf).symm

end Blotto
