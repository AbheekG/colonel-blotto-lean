import Blotto.RealUniformHead

/-! A fresh source head can be separated while retaining an independent
continuation block. This is the exact product identity used by resource gluing. -/

namespace Blotto.RealUniformInputs
open MeasureTheory

def productJoin {S : Type*} (C : ℕ) (z : ℝ × ((Fin C → ℝ) × S)) : (Fin (C + 1) → ℝ) × S :=
  (join (z.1, z.2.1), z.2.2)

theorem productJoin_measurable {S : Type*} [MeasurableSpace S] (C : ℕ) :
    Measurable (productJoin (S := S) C) :=
  ((measurable_join C).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd)

def productSplit {S : Type*} (C : ℕ) (z : (Fin (C + 1) → ℝ) × S) : ℝ × ((Fin C → ℝ) × S) :=
  (z.1 0, Fin.tail z.1, z.2)

theorem productSplit_measurable {S : Type*} [MeasurableSpace S] (C : ℕ) :
    Measurable (productSplit (S := S) C) :=
  ((measurable_pi_apply 0).comp measurable_fst).prodMk
    (((measurable_tail C).comp measurable_fst).prodMk measurable_snd)

theorem productJoin_law {S : Type*} [MeasurableSpace S] (C : ℕ) (ν : Measure S) [SFinite ν] :
    Measure.map (productJoin C) ((unitUniform : Measure ℝ).prod ((law C : Measure (Fin C → ℝ)).prod ν)) =
      (law (C + 1) : Measure (Fin (C + 1) → ℝ)).prod ν := by
  rw [← Measure.prodAssoc_prod, Measure.map_map (productJoin_measurable C) MeasurableEquiv.prodAssoc.measurable]
  change Measure.map (Prod.map join id) (((unitUniform : Measure ℝ).prod (law C : Measure (Fin C → ℝ))).prod ν) = _
  rw [← Measure.map_prod_map _ _ (measurable_join C) measurable_id, Measure.map_id]
  rfl

theorem map_product_succ {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
    (C : ℕ) (ν : Measure S) [SFinite ν] (f : ((Fin (C + 1) → ℝ) × S) → α) (hf : Measurable f) :
    Measure.map f ((law (C + 1) : Measure (Fin (C + 1) → ℝ)).prod ν) =
      Measure.map (f ∘ productJoin C) ((unitUniform : Measure ℝ).prod ((law C : Measure (Fin C → ℝ)).prod ν)) := by
  rw [← productJoin_law C ν, Measure.map_map hf (productJoin_measurable C)]

end Blotto.RealUniformInputs
