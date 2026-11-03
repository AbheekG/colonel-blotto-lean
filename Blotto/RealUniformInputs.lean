import Blotto.RealIndependentChoice

/-! Finite vectors of independent continuous unit-uniform inputs. The head
and tail decomposition is an exact product law, used by adaptive execution. -/

namespace Blotto.RealUniformInputs
open MeasureTheory

noncomputable def productLaw {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : ProbabilityMeasure (α × β) :=
  ⟨(μ : Measure α).prod (ν : Measure β), inferInstance⟩

def join {C : ℕ} (z : ℝ × (Fin C → ℝ)) : Fin (C + 1) → ℝ := Fin.cons z.1 z.2
def split {C : ℕ} (seed : Fin (C + 1) → ℝ) : ℝ × (Fin C → ℝ) := (seed 0, Fin.tail seed)

theorem measurable_join (C : ℕ) : Measurable (join (C := C)) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact measurable_fst
  · exact (measurable_pi_apply i).comp measurable_snd

theorem measurable_split (C : ℕ) : Measurable (split (C := C)) := by
  apply Measurable.prodMk
  · exact measurable_pi_apply 0
  · apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.succ

theorem split_join {C : ℕ} (z : ℝ × (Fin C → ℝ)) : split (join z) = z := by
  rcases z with ⟨u, tail⟩
  rfl

theorem join_split {C : ℕ} (seed : Fin (C + 1) → ℝ) : join (split seed) = seed := Fin.cons_self_tail seed

noncomputable def law : (C : ℕ) → ProbabilityMeasure (Fin C → ℝ)
  | 0 => ⟨Measure.dirac (fun j => Fin.elim0 j), inferInstance⟩
  | C + 1 => (productLaw unitUniform (law C)).map join

theorem law_split (C : ℕ) :
    Measure.map split (law (C + 1) : Measure (Fin (C + 1) → ℝ)) =
      (unitUniform : Measure ℝ).prod (law C : Measure (Fin C → ℝ)) := by
  change Measure.map split (Measure.map join ((unitUniform : Measure ℝ).prod (law C : Measure (Fin C → ℝ)))) = _
  rw [Measure.map_map (measurable_split C) (measurable_join C)]
  have hId : split ∘ join = (id : (ℝ × (Fin C → ℝ)) → (ℝ × (Fin C → ℝ))) := funext split_join
  rw [hId, Measure.map_id]

theorem map_law_succ {α : Type*} [MeasurableSpace α] (C : ℕ) (f : (Fin (C + 1) → ℝ) → α)
    (hF : Measurable f) :
    Measure.map f (law (C + 1) : Measure (Fin (C + 1) → ℝ)) =
      Measure.map (f ∘ join) ((unitUniform : Measure ℝ).prod (law C : Measure (Fin C → ℝ))) := by
  change Measure.map f (Measure.map join ((unitUniform : Measure ℝ).prod (law C : Measure (Fin C → ℝ)))) = _
  rw [Measure.map_map hF (measurable_join C)]

end Blotto.RealUniformInputs
