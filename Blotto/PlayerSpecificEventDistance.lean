import Blotto.PlayerSpecificFiniteSamplerNash

/-! Total variation is the supremum of absolute probability differences
over measurable events. All hybrid comparisons concern whole allocation
laws with finite scalar packets, retaining within-player dependence. -/
namespace Blotto.PlayerSpecificEventDistance
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Bound {α : Type*} [MeasurableSpace α] (u l : ProbabilityMeasure α) (E : ℝ) : Prop :=
  ∀ A : Set α,MeasurableSet A → |(u : Measure α).real A-(l : Measure α).real A| ≤ E

noncomputable def distance {α : Type*} [MeasurableSpace α] (u l : ProbabilityMeasure α) : ℝ :=
  sSup {d : ℝ | ∃ A : Set α,MeasurableSet A ∧ d=|(u : Measure α).real A-(l : Measure α).real A|}

theorem distance_le {α : Type*} [MeasurableSpace α] (u l : ProbabilityMeasure α) (E : ℝ) (h : Bound u l E) : distance u l ≤ E := by
  apply csSup_le
  · refine ⟨0,∅,MeasurableSet.empty,?_⟩
    simp
  · intro d hd
    obtain ⟨A,hA,rfl⟩ := hd
    exact h A hA

theorem symm {α : Type*} [MeasurableSpace α] (u l : ProbabilityMeasure α) (E : ℝ) (h : Bound u l E) : Bound l u E := by
  intro A hA
  rw [abs_sub_comm]
  exact h A hA

theorem triangle {α : Type*} [MeasurableSpace α] (u m l : ProbabilityMeasure α) (E D : ℝ)
    (hu : Bound u m E) (hl : Bound m l D) : Bound u l (E+D) := by
  intro A hA
  exact (abs_sub_le _ _ _).trans (add_le_add (hu A hA) (hl A hA))

theorem mono {α : Type*} [MeasurableSpace α] (u l : ProbabilityMeasure α) (E D : ℝ)
    (h : Bound u l E) (he : E ≤ D) : Bound u l D := fun A hA => (h A hA).trans he

theorem map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (u l : ProbabilityMeasure α) (E : ℝ)
    (h : Bound u l E) (f : α → β) (hf : Measurable f) : Bound (u.map f) (l.map f) E := by
  intro A hA
  change |(Measure.map f (u : Measure α)).real A-(Measure.map f (l : Measure α)).real A| ≤ E
  rw [map_measureReal_apply hf hA,map_measureReal_apply hf hA]
  exact h (f ⁻¹' A) (hA.preimage hf)

end Blotto.PlayerSpecificEventDistance
