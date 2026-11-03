import Blotto.NestedSpec
import Blotto.ResourceRounding
import Blotto.CoordinatePermutation

/-! Explicit mathematical terminal construction for three nested resource
coordinates. Only one coordinate may still use an interior mixture weight. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure TerminalResources where
  M : ℝ
  long : Allocation 3
  short : Allocation 3
  resource : Allocation 3
  short_pos : ∀ j, 0 < short j
  short_lt : ∀ j, short j < long j
  long_le : ∀ j, long j ≤ M
  box : InBox (fun j => long j - short j) resource
  fractional_le : (fractionalSet (fun j => long j - short j) resource).card ≤ 1
  mean : (∑ j, (long j - resource j)) = 2 * M

namespace TerminalResources

noncomputable def capacity (i : TerminalResources) : Allocation 3 := fun j => i.long j - i.short j
noncomputable def weight (i : TerminalResources) (j : Fin 3) : ℝ := i.resource j / i.capacity j
noncomputable def endpoint (i : TerminalResources) (j : Fin 3) : ℝ :=
  if i.resource j = 0 then i.long j else i.short j

noncomputable def focus (i : TerminalResources) : Fin 3 := by
  classical
  exact if Fractional i.capacity i.resource 0 then 0 else if Fractional i.capacity i.resource 1 then 1 else 2

noncomputable def permutation (i : TerminalResources) : Equiv.Perm (Fin 3) := Equiv.swap i.focus 2

theorem capacity_pos (i : TerminalResources) (j : Fin 3) : 0 < i.capacity j := sub_pos.mpr (i.short_lt j)

theorem weight_bounds (i : TerminalResources) (j : Fin 3) : 0 ≤ i.weight j ∧ i.weight j ≤ 1 :=
  ⟨div_nonneg (i.box j).1 (le_of_lt (i.capacity_pos j)), (div_le_one (i.capacity_pos j)).mpr (i.box j).2⟩

theorem fractional_unique (i : TerminalResources) {a b : Fin 3}
    (ha : Fractional i.capacity i.resource a) (hb : Fractional i.capacity i.resource b) : a = b := by
  by_contra hn
  have hc : 1 < (fractionalSet i.capacity i.resource).card := Finset.one_lt_card.mpr
    ⟨a, (mem_fractionalSet _ _ _).mpr ha, b, (mem_fractionalSet _ _ _).mpr hb, hn⟩
  have hl : (fractionalSet i.capacity i.resource).card ≤ 1 := i.fractional_le
  omega

theorem fractional_focus (i : TerminalResources) {j : Fin 3}
    (hj : Fractional i.capacity i.resource j) : j = i.focus := by
  classical
  unfold focus
  split_ifs with h0 h1
  · exact i.fractional_unique hj h0
  · exact i.fractional_unique hj h1
  · fin_cases j
    · exact (h0 hj).elim
    · exact (h1 hj).elim
    · rfl

theorem permutation_last (i : TerminalResources) : i.permutation 2 = i.focus := by simp [permutation]

theorem permutation_other (i : TerminalResources) {j : Fin 3} (hj : j ≠ 2) : i.permutation j ≠ i.focus := by
  intro h
  exact hj (i.permutation.injective (h.trans i.permutation_last.symm))

theorem endpoint_resource (i : TerminalResources) {j : Fin 3} (hj : j ≠ i.focus) :
    i.endpoint j = i.long j - i.resource j := by
  have hf : ¬Fractional i.capacity i.resource j := fun h => hj (i.fractional_focus h)
  unfold endpoint
  split_ifs with h0
  · simp [h0]
  · have hp : 0 < i.resource j := lt_of_le_of_ne (i.box j).1 (Ne.symm h0)
    have hc : i.resource j = i.capacity j := by
      have hn : ¬i.resource j < i.capacity j := fun h => hf ⟨hp, h⟩
      exact le_antisymm (i.box j).2 (le_of_not_gt hn)
    dsimp [capacity] at hc
    linarith

theorem endpoint_bounds (i : TerminalResources) (j : Fin 3) :
    0 < i.endpoint j ∧ i.endpoint j ≤ i.M := by
  unfold endpoint
  split_ifs
  · exact ⟨lt_trans (i.short_pos j) (i.short_lt j), i.long_le j⟩
  · exact ⟨i.short_pos j, le_trans (le_of_lt (i.short_lt j)) (i.long_le j)⟩

theorem mixture_mean (i : TerminalResources) (j : Fin 3) :
    i.weight j * i.short j + (1 - i.weight j) * i.long j = i.long j - i.resource j := by
  dsimp [weight]
  field_simp [ne_of_gt (i.capacity_pos j)]
  dsimp [capacity]
  ring

noncomputable def input (i : TerminalResources) : NestedSpec where
  M := i.M
  a := i.endpoint (i.permutation 0)
  d := i.endpoint (i.permutation 1)
  c := i.long i.focus
  t := i.short i.focus
  q := i.weight i.focus
  a_pos := (i.endpoint_bounds _).1
  d_pos := (i.endpoint_bounds _).1
  c_pos := lt_trans (i.short_pos _) (i.short_lt _)
  t_pos := i.short_pos _
  t_lt := i.short_lt _
  q_nonneg := (i.weight_bounds _).1
  q_le := (i.weight_bounds _).2
  a_le := (i.endpoint_bounds _).2
  d_le := (i.endpoint_bounds _).2
  c_le := i.long_le _
  balance := by
    rw [i.endpoint_resource (i.permutation_other (by decide : (0 : Fin 3) ≠ 2)),
      i.endpoint_resource (i.permutation_other (by decide : (1 : Fin 3) ≠ 2))]
    have hmix := i.mixture_mean i.focus
    have hs := Equiv.sum_comp i.permutation (fun j => i.long j - i.resource j)
    rw [i.mean] at hs
    simp [Fin.sum_univ_succ, i.permutation_last] at hs
    linarith

noncomputable def law (i : TerminalResources) : Mixed 3 := permuteLaw i.permutation i.input.law

/-- A zero or saturated resource coordinate uses its exact endpoint uniform. -/
theorem endpoint_measure (i : TerminalResources) {j : Fin 3} (hj : j ≠ i.focus) :
    affineMeasure (i.weight j) (uniformLaw (i.short j)) (uniformLaw (i.long j)) = uniformLaw (i.endpoint j) := by
  have hf : ¬Fractional i.capacity i.resource j := fun h => hj (i.fractional_focus h)
  unfold endpoint
  split_ifs with h0
  · simp [weight, h0, affineMeasure]
  · have hp : 0 < i.resource j := lt_of_le_of_ne (i.box j).1 (Ne.symm h0)
    have hc : i.resource j = i.capacity j := by
      have hn : ¬i.resource j < i.capacity j := fun h => hf ⟨hp, h⟩
      exact le_antisymm (i.box j).2 (le_of_not_gt hn)
    simp [weight, hc, ne_of_gt (i.capacity_pos j), affineMeasure]

theorem law_contract (i : TerminalResources) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 3)), FullBudget i.M x) ∧
      ∀ j, (marginal i.law j : Measure ℝ) = affineMeasure (i.weight j)
        (uniformLaw (i.short j)) (uniformLaw (i.long j)) := by
  have hm := i.input.law_contract
  refine ⟨permuteLaw_fullBudget i.permutation hm.1, ?_⟩
  intro j
  rw [law, permuteLaw_marginal]
  by_cases hj : i.permutation j = 2
  · have hjf : j = i.focus := by
      have h := congrArg i.permutation hj
      simpa [permutation] using h
    rw [hj, hjf, hm.2.2.2]
    rfl
  · rw [i.endpoint_measure (by
      intro h
      have he := congrArg i.permutation h
      apply hj
      simpa [permutation] using he)]
    have hidx : i.permutation j = 0 ∨ i.permutation j = 1 := by
      generalize he : i.permutation j = k at hj ⊢
      fin_cases k <;> simp_all
    rcases hidx with h0 | h1
    · rw [h0, hm.2.1]
      change uniformLaw (i.endpoint (i.permutation 0)) = _
      have he := congrArg i.permutation h0
      simpa [permutation] using (congrArg (fun k => uniformLaw (i.endpoint k)) he).symm
    · rw [h1, hm.2.2.1]
      change uniformLaw (i.endpoint (i.permutation 1)) = _
      have he := congrArg i.permutation h1
      simpa [permutation] using (congrArg (fun k => uniformLaw (i.endpoint k)) he).symm

noncomputable def point (i : TerminalResources) (useFamily : Bool) (r t : ℝ)
    (edge : Fin 9) (residualEdge : Fin 3) : Allocation 3 :=
  permuteAllocation i.permutation (i.input.point useFamily r t edge residualEdge)

theorem point_fullBudget (i : TerminalResources) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.M (i.point useFamily r t edge residualEdge) :=
  permuteAllocation_fullBudget i.permutation (i.input.point_fullBudget useFamily hr ht edge residualEdge)

theorem endpoint_long (i : TerminalResources) (j : Fin 3) : i.endpoint j ≤ i.long j := by
  unfold endpoint
  split_ifs
  · exact le_rfl
  · exact le_of_lt (i.short_lt j)

theorem point_inBox (i : TerminalResources) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    InBox i.long (i.point useFamily r t edge residualEdge) := by
  have hb := i.input.point_inBox useFamily hr ht edge residualEdge
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

end TerminalResources
end Blotto
