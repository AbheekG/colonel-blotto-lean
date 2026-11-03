import Blotto.RealUniformInputs

/-! The interpolation/head primitive in a flat continuous seed has the
actual unit-uniform law, with the unused tail independent. -/

namespace Blotto.RealUniformInputs
open MeasureTheory

theorem head_law (C : ℕ) :
    Measure.map (fun seed : Fin (C + 1) → ℝ => seed 0) (law (C + 1) : Measure (Fin (C + 1) → ℝ)) =
      (unitUniform : Measure ℝ) := by
  change Measure.map (Prod.fst ∘ split) _ = _
  rw [← Measure.map_map measurable_fst (measurable_split C), law_split,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem tail_law (C : ℕ) :
    Measure.map (Fin.tail : (Fin (C + 1) → ℝ) → (Fin C → ℝ))
      (law (C + 1) : Measure (Fin (C + 1) → ℝ)) = (law C : Measure (Fin C → ℝ)) := by
  change Measure.map (Prod.snd ∘ split) _ = _
  rw [← Measure.map_map measurable_snd (measurable_split C), law_split,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem measurable_tail (C : ℕ) :
    Measurable (Fin.tail : (Fin (C + 1) → ℝ) → (Fin C → ℝ)) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply j.succ

end Blotto.RealUniformInputs
