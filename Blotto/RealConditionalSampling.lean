import Blotto.ParameterLaw

/-! A measurable sampler with fresh independent input realizes the actual
conditional average, rather than only its separately specified marginals. -/

namespace Blotto
open MeasureTheory

theorem map_product_conditional {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (sample : α → β → γ) (hSample : Measurable (Function.uncurry sample)) :
    Measure.map (Function.uncurry sample) (μ.prod ν) =
      μ.bind (fun a => Measure.map (sample a) ν) := by
  rw [Measure.prod, map_bind_family _ _ Measurable.map_prodMk_left _ hSample]
  congr 1
  funext a
  rw [Measure.map_map hSample measurable_prodMk_left]
  rfl

theorem map_product_realizes_family {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (sample : α → β → γ) (hSample : Measurable (Function.uncurry sample))
    (law : α → Measure γ) (hLaw : ∀ a, Measure.map (sample a) ν = law a) :
    Measure.map (Function.uncurry sample) (μ.prod ν) = μ.bind law := by
  rw [map_product_conditional μ ν sample hSample]
  congr 1
  funext a
  exact hLaw a

end Blotto
