import Blotto.RealUniformHead

/-! Fixed trailing input blocks retain the exact independent uniform law.
This supplies equal-sized continuation interfaces without resampling. -/

namespace Blotto.RealUniformInputs
open MeasureTheory

def dropInputs (C : ℕ) : (D : ℕ) → (Fin (C + D) → ℝ) → (Fin C → ℝ)
  | 0, seed => seed
  | D + 1, seed => dropInputs C D (Fin.tail seed)

theorem dropInputs_measurable (C D : ℕ) : Measurable (dropInputs C D) := by
  induction D with
  | zero => exact measurable_id
  | succ D ih => exact ih.comp (measurable_tail (C + D))

theorem dropInputs_law (C D : ℕ) :
    Measure.map (dropInputs C D) (law (C + D) : Measure (Fin (C + D) → ℝ)) =
      (law C : Measure (Fin C → ℝ)) := by
  induction D with
  | zero => exact Measure.map_id
  | succ D ih =>
    change Measure.map (dropInputs C D ∘ Fin.tail) (law ((C + D) + 1) : Measure (Fin ((C + D) + 1) → ℝ)) = _
    rw [← Measure.map_map (dropInputs_measurable C D) (measurable_tail (C + D)), tail_law, ih]

theorem dropInputs_bounds (C D : ℕ) (seed : Fin (C + D) → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : ∀ j, 0 ≤ dropInputs C D seed j ∧ dropInputs C D seed j ≤ 1 := by
  induction D with
  | zero => exact h
  | succ D ih =>
    exact ih (Fin.tail seed) (fun j => h j.succ)

end Blotto.RealUniformInputs
