import Blotto.NestedFirstGeometry

/-! Explicit conditional whole-allocation laws for the first nested case,
including the zero-probability corner. The law is measurable before averaging. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter

noncomputable def firstZeroLaw (i : NestedInput) (s : ℝ) : Mixed 3 :=
  segmentLaw ![0, i.d, s] ![i.a, 0, s]

theorem firstZeroLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : i.conditionalProbability s = 0) :
    ∀ᵐ x ∂(i.firstZeroLaw s : Measure (Allocation 3)), FullBudget i.M x := by
  have he := i.conditional_zero htv hs hp
  apply segmentLaw_fullBudget
  · exact fullBudget_three (le_refl 0) (le_of_lt i.d_pos) hs.1 (by linarith [he.2.2.2])
  · exact fullBudget_three (le_of_lt i.a_pos) (le_refl 0) hs.1 (by linarith [he.2.2.1])

theorem firstZeroLaw_marginals (i : NestedInput) (s : ℝ) (hp : i.conditionalProbability s = 0) :
    (marginal (i.firstZeroLaw s) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.firstZeroLaw s) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.firstZeroLaw s) 2 : Measure ℝ) = i.conditionalThirdLaw s := by
  have hx : ∀ {a : ℝ}, 0 < a → (affineUniform 0 a : Measure ℝ) = uniformLaw a := by
    intro a ha
    rw [affineUniform_increasing ha]
    simp only [intervalLaw, sub_zero, uniformLaw]
  simp [firstZeroLaw, segmentLaw_marginal, affineUniform_constant,
    conditionalThirdLaw, hp, hx i.a_pos]
  rw [affineUniform_reverse i.d 0, hx i.d_pos]

noncomputable def positiveParameters (i : NestedInput) : Set ℝ :=
  Icc 0 i.t ∩ {s | 0 < i.conditionalProbability s}

theorem measurableSet_positiveParameters (i : NestedInput) : MeasurableSet i.positiveParameters :=
  measurableSet_Icc.inter (measurableSet_lt measurable_const i.measurable_conditionalProbability)

noncomputable def firstConditionalLaw (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) : Mixed 3 :=
  by
    classical
    exact if h : s ∈ i.positiveParameters then i.firstPositiveLaw htv s h.1 h.2 else i.firstZeroLaw s

theorem measurable_firstZeroLaw (i : NestedInput) :
    Measurable (fun s => (i.firstZeroLaw s : Measure (Allocation 3))) := by
  apply measurable_segmentLaw_family
  all_goals apply Measurable.of_eval
  all_goals intro j
  all_goals fin_cases j
  all_goals first | exact measurable_const | exact measurable_id

theorem measurable_firstPositiveFamily (i : NestedInput) (htv : i.t ≤ i.v) :
    Measurable (fun s : i.positiveParameters =>
      (i.firstPositiveLaw htv s s.property.1 s.property.2 : Measure (Allocation 3))) := by
  apply ThreeGeometry.measurable_shifted_couplingLaw_family
    (fun s : i.positiveParameters => i.firstGeometry htv s s.property.1 s.property.2)
    measurable_subtype_coe
  all_goals dsimp [firstGeometry]
  all_goals fun_prop

theorem measurable_firstConditionalLaw (i : NestedInput) (htv : i.t ≤ i.v) :
    Measurable (fun s => (i.firstConditionalLaw htv s : Measure (Allocation 3))) := by
  classical
  have he : (fun s => (i.firstConditionalLaw htv s : Measure (Allocation 3))) =
      (fun s => if h : s ∈ i.positiveParameters then
        (i.firstPositiveLaw htv s h.1 h.2 : Measure (Allocation 3)) else
        (i.firstZeroLaw s : Measure (Allocation 3))) := by
    funext s
    unfold firstConditionalLaw
    split_ifs <;> rfl
  rw [he]
  exact (i.measurable_firstPositiveFamily htv).dite
    (i.measurable_firstZeroLaw.comp measurable_subtype_coe) i.measurableSet_positiveParameters

theorem firstConditionalLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) :
    ∀ᵐ x ∂(i.firstConditionalLaw htv s : Measure (Allocation 3)), FullBudget i.M x := by
  classical
  unfold firstConditionalLaw
  split_ifs with hp
  · exact i.firstPositiveLaw_fullBudget htv s hp.1 hp.2
  · have hn : i.conditionalProbability s = 0 := by
      have hbounds := i.conditional_bounds htv hs
      have hn : ¬0 < i.conditionalProbability s := fun h => hp ⟨hs, h⟩
      linarith
    exact i.firstZeroLaw_fullBudget htv hs hn

theorem firstConditionalLaw_marginals (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) :
    (marginal (i.firstConditionalLaw htv s) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.firstConditionalLaw htv s) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.firstConditionalLaw htv s) 2 : Measure ℝ) = i.conditionalThirdLaw s := by
  classical
  unfold firstConditionalLaw
  split_ifs with hp
  · exact i.firstPositiveLaw_marginals htv s hp.1 hp.2
  · have hn : i.conditionalProbability s = 0 := by
      have hbounds := i.conditional_bounds htv hs
      have hn : ¬0 < i.conditionalProbability s := fun h => hp ⟨hs, h⟩
      linarith
    exact i.firstZeroLaw_marginals s hn

noncomputable def firstLaw (i : NestedInput) (htv : i.t ≤ i.v) : Mixed 3 :=
  averagedLaw i.locationLaw (i.firstConditionalLaw htv) (i.measurable_firstConditionalLaw htv)

theorem firstLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) :
    ∀ᵐ x ∂(i.firstLaw htv : Measure (Allocation 3)), FullBudget i.M x := by
  apply averagedLaw_fullBudget
  exact i.locationLaw_supported.mono fun _ hs => i.firstConditionalLaw_fullBudget htv hs

theorem firstLaw_marginals (i : NestedInput) (htv : i.t ≤ i.v) :
    (marginal (i.firstLaw htv) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.firstLaw htv) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.firstLaw htv) 2 : Measure ℝ) = i.nestedTargetLaw := by
  constructor
  · apply averagedLaw_marginal_constant
    exact i.locationLaw_supported.mono fun _ hs => (i.firstConditionalLaw_marginals htv hs).1
  constructor
  · apply averagedLaw_marginal_constant
    exact i.locationLaw_supported.mono fun _ hs => (i.firstConditionalLaw_marginals htv hs).2.1
  · rw [firstLaw, averagedLaw_marginal]
    have he : (fun s => (marginal (i.firstConditionalLaw htv s) 2 : Measure ℝ)) =ᵐ[
        (i.locationLaw : Measure ℝ)] i.conditionalThirdLaw :=
      i.locationLaw_supported.mono fun _ hs => (i.firstConditionalLaw_marginals htv hs).2.2
    rw [Measure.bind_congr_right he]
    exact i.averagedThirdLaw_eq_target htv

/-- The first case of Lemma 2.3 has a complete actual joint-law contract. -/
theorem first_coupling_contract (i : NestedInput) (htv : i.t ≤ i.v) :
    (∀ᵐ x ∂(i.firstLaw htv : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal (i.firstLaw htv) 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal (i.firstLaw htv) 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal (i.firstLaw htv) 2 : Measure ℝ) = i.nestedTargetLaw :=
  ⟨i.firstLaw_fullBudget htv, i.firstLaw_marginals htv⟩

/-- An explicit output path: select a segment, then interpolate with the
second unit-uniform parameter. The first unit-uniform parameter sets s. -/
noncomputable def firstPoint (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (edge : Fin 9) (t : ℝ) : Allocation 3 := by
  classical
  exact if hs : s ∈ i.positiveParameters then
    shiftThird s ((i.firstGeometry htv s hs.1 hs.2).couplingPoint edge t)
  else segmentPoint ![0, i.d, s] ![i.a, 0, s] t

theorem firstPoint_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {s t : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    FullBudget i.M (i.firstPoint htv s edge t) := by
  classical
  unfold firstPoint
  split_ifs with hp
  · have he := i.firstGeometry_matches htv s hp.1 hp.2
    have hb : (i.firstGeometry htv s hp.1 hp.2).budget + s = i.M := by linarith [he.2.2.2.1]
    simpa only [hb] using shiftThird_fullBudget hs.1
      ((i.firstGeometry htv s hp.1 hp.2).couplingPoint_fullBudget edge ht)
  · have hz : i.conditionalProbability s = 0 := by
      have hbounds := i.conditional_bounds htv hs
      have hn : ¬0 < i.conditionalProbability s := fun h => hp ⟨hs, h⟩
      linarith
    have he := i.conditional_zero htv hs hz
    exact segment_fullBudget
      (fullBudget_three (le_refl 0) (le_of_lt i.d_pos) hs.1 (by linarith [he.2.2.2]))
      (fullBudget_three (le_of_lt i.a_pos) (le_refl 0) hs.1 (by linarith [he.2.2.1])) ht

/-- This includes both endpoint random paths and every possible segment slot,
so the budget conclusion does not rest on an almost-sure shortcut. -/
theorem firstSamplePath_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    FullBudget i.M (i.firstPoint htv (i.location r) edge t) :=
  i.firstPoint_fullBudget htv (i.location_bounds hr) ht edge

end Blotto.NestedInput
