import Blotto.RealSamplerBoxes
import Blotto.TerminalResources

/-! Exact execution of a valid three-resource terminal. Its permutation,
whole law and every-path coordinate caps match the existing construction. -/

namespace Blotto.TerminalResources
open MeasureTheory

noncomputable def realSample (i : TerminalResources) (seed : Fin 11 → ℝ) : Allocation 3 :=
  permuteAllocation i.permutation (i.input.realSample seed)

theorem realSample_measurable (i : TerminalResources) : Measurable i.realSample :=
  (measurable_permuteAllocation i.permutation).comp i.input.realSample_measurable

theorem realSample_law (i : TerminalResources) :
    Measure.map i.realSample (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.law : Measure (Allocation 3)) := by
  change Measure.map (permuteAllocation i.permutation ∘ i.input.realSample) _ = _
  rw [← Measure.map_map (measurable_permuteAllocation i.permutation) i.input.realSample_measurable,
    i.input.realSample_law]
  rfl

theorem realSample_fullBudget (i : TerminalResources) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (i.realSample seed) :=
  permuteAllocation_fullBudget i.permutation (i.input.realSample_fullBudget seed h)

theorem realSample_inBox (i : TerminalResources) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox i.long (i.realSample seed) := by
  have hb := i.input.realSample_inBox seed h
  have hp := permuteAllocation_inBox i.permutation hb
  apply inBox_mono _ hp
  intro j
  change ![i.endpoint (i.permutation 0), i.endpoint (i.permutation 1), i.long i.focus]
    (i.permutation j) ≤ i.long j
  by_cases hj : i.permutation j = 2
  · have he : j = i.focus := by
      have he := congrArg i.permutation hj
      simpa [permutation] using he
    rw [hj, he]
    exact le_rfl
  · have hidx : i.permutation j = 0 ∨ i.permutation j = 1 := by
      generalize he : i.permutation j = k at hj ⊢
      fin_cases k <;> simp_all
    rcases hidx with h0 | h1
    · rw [h0]
      have he := congrArg i.permutation h0
      have hji : j = i.permutation 0 := by simpa [permutation] using he
      simpa [hji] using i.endpoint_long (i.permutation 0)
    · rw [h1]
      have he := congrArg i.permutation h1
      have hji : j = i.permutation 1 := by simpa [permutation] using he
      simpa [hji] using i.endpoint_long (i.permutation 1)

theorem realSample_marginals (i : TerminalResources) (j : Fin 3) :
    Measure.map (fun seed => i.realSample seed j) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      affineMeasure (i.weight j) (uniformLaw (i.short j)) (uniformLaw (i.long j)) := by
  change Measure.map ((fun x : Allocation 3 => x j) ∘ i.realSample) _ = _
  rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
  exact i.law_contract.2 j

end Blotto.TerminalResources
