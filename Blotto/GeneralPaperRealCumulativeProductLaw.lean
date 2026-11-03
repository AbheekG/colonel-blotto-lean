import Blotto.GeneralPaperRealCumulativeChoiceLaw

/-! One uniform categorical choice with an independent continuation has
the exact mixture of the continuation's whole output laws. -/
namespace Blotto.GeneralPaperRealCumulativeChoice
open MeasureTheory
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem product_law {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (address : ℕ)
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (ν : Measure β) [SFinite ν] (f : Fin r × β → α) (hf : Measurable f) :
    Measure.map (fun z : ℝ × β => f ((manyRun w hr address z.1).value, z.2))
      ((unitUniform : Measure ℝ).prod ν) =
      Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.map (fun b => f (i, b)) ν) := by
  let g := fun u => (manyRun w hr address u).value
  have hg : Measurable g := manyRun_measurable w hr address
  have hm := (Measure.map_prod_map (unitUniform : Measure ℝ) ν hg measurable_id).symm
  rw [Measure.map_id, manyRun_law w hr hw hs address] at hm
  have he : (fun z : ℝ × β => f ((manyRun w hr address z.1).value, z.2)) = f ∘ Prod.map g id := rfl
  rw [he, ← Measure.map_map hf (hg.prodMap measurable_id), hm]
  change Measure.map f ((Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)).prod ν) = _
  rw [Measure.prod_sum_left, Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.prod_smul_left, Measure.map_smul _ hf.aemeasurable,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

end Blotto.GeneralPaperRealCumulativeChoice
