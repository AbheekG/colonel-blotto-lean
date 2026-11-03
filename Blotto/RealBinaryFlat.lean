import Blotto.RealChoiceTree
import Blotto.BinaryMixture

/-! A fresh first uniform selects a single continuation. The retained tail
has the exact independent law used by either continuation. -/

namespace Blotto
open MeasureTheory
open scoped Classical

noncomputable def realBinarySample {α : Type*} (p : ℝ) {C : ℕ}
    (upper lower : (Fin C → ℝ) → α) (seed : Fin (C + 1) → ℝ) : α :=
  if seed 0 ≤ p then upper (Fin.tail seed) else lower (Fin.tail seed)

theorem realBinarySample_measurable {α : Type*} [MeasurableSpace α] (p : ℝ) {C : ℕ}
    (upper lower : (Fin C → ℝ) → α) (hUpper : Measurable upper) (hLower : Measurable lower) :
    Measurable (realBinarySample p upper lower) := by
  have hCompose := (RealIndependentChoice.measurable_sample p upper lower hUpper hLower).comp
    (RealUniformInputs.measurable_split C)
  exact hCompose

theorem realBinarySample_law {α : Type*} [MeasurableSpace α] (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) {C : ℕ}
    (upper lower : (Fin C → ℝ) → α) (hUpper : Measurable upper) (hLower : Measurable lower) :
    Measure.map (realBinarySample p upper lower) (RealUniformInputs.law (C + 1) : Measure (Fin (C + 1) → ℝ)) =
      ENNReal.ofReal p • Measure.map upper (RealUniformInputs.law C : Measure (Fin C → ℝ)) +
        ENNReal.ofReal (1 - p) • Measure.map lower (RealUniformInputs.law C : Measure (Fin C → ℝ)) := by
  rw [RealUniformInputs.map_law_succ C _ (realBinarySample_measurable p upper lower hUpper hLower)]
  change Measure.map (RealIndependentChoice.sample p upper lower) _ = _
  exact RealIndependentChoice.map_product p hp (RealUniformInputs.law C) upper lower hUpper hLower

theorem realBinarySample_realizes {n C : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : (Fin C → ℝ) → Allocation n) (hUpper : Measurable upper) (hLower : Measurable lower)
    (μ ν : Mixed n)
    (hμ : Measure.map upper (RealUniformInputs.law C : Measure (Fin C → ℝ)) = (μ : Measure (Allocation n)))
    (hν : Measure.map lower (RealUniformInputs.law C : Measure (Fin C → ℝ)) = (ν : Measure (Allocation n))) :
    Measure.map (realBinarySample p upper lower) (RealUniformInputs.law (C + 1) : Measure (Fin (C + 1) → ℝ)) =
      (binaryLaw p hp μ ν : Measure (Allocation n)) := by
  rw [realBinarySample_law p hp upper lower hUpper hLower, hμ, hν]
  exact (binaryLaw_measure p hp μ ν).symm

theorem realBinarySample_predicate {α : Type*} (p : ℝ) {C : ℕ}
    (upper lower : (Fin C → ℝ) → α) (seed : Fin (C + 1) → ℝ) (P : α → Prop)
    (hUpper : P (upper (Fin.tail seed))) (hLower : P (lower (Fin.tail seed))) :
    P (realBinarySample p upper lower seed) := by
  unfold realBinarySample
  split_ifs <;> assumption

end Blotto
