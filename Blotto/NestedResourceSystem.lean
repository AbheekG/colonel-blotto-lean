import Blotto.TerminalResources
import Blotto.UniformSupport

/-! An actual constant-sum coupling of three nested marginal mixtures, by
at most two pairwise updates followed by the explicit terminal construction. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

structure NestedResourceSystem where
  M : ℝ
  long : Allocation 3
  short : Allocation 3
  initial : Allocation 3
  short_pos : ∀ j, 0 < short j
  short_lt : ∀ j, short j < long j
  long_le : ∀ j, long j ≤ M
  initial_box : InBox (fun j => long j - short j) initial
  initial_mean : (∑ j, (long j - initial j)) = 2 * M

namespace NestedResourceSystem

noncomputable def capacity (i : NestedResourceSystem) : Allocation 3 := fun j => i.long j - i.short j
noncomputable def initialWeight (i : NestedResourceSystem) (j : Fin 3) : ℝ := i.initial j / i.capacity j

def Valid (i : NestedResourceSystem) (r : Allocation 3) : Prop :=
  InBox i.capacity r ∧ (fractionalSet i.capacity r).card ≤ 1 ∧ (∑ j, (i.long j - r j)) = 2 * i.M

noncomputable def terminal (i : NestedResourceSystem) (r : Allocation 3) (hr : i.Valid r) : TerminalResources :=
  ⟨i.M, i.long, i.short, r, i.short_pos, i.short_lt, i.long_le, hr.1, hr.2.1, hr.2.2⟩

noncomputable def leafLaw (i : NestedResourceSystem) (r : Allocation 3) : Mixed 3 := by
  classical
  exact if hr : i.Valid r then (i.terminal r hr).law else segmentLaw 0 0

noncomputable def tree (i : NestedResourceSystem) : RoundingTree 3 :=
  roundResources i.capacity (selectThreePair i.capacity) 2 i.initial

theorem tree_valid (i : NestedResourceSystem) : i.tree.ForLeaves i.Valid := by
  have ht := roundResources_leaves i.capacity i.initial (selectThreePair i.capacity) 2
    i.initial_box (by exact (Finset.card_le_univ _).trans (by simp))
  apply i.tree.forLeaves_mono _ ht
  intro r hr
  refine ⟨hr.1, hr.2.2, ?_⟩
  rw [Finset.sum_sub_distrib, hr.2.1, ← Finset.sum_sub_distrib]
  exact i.initial_mean

theorem tree_height (i : NestedResourceSystem) : i.tree.height ≤ 2 :=
  roundResources_height _ _ _ _

theorem tree_average (i : NestedResourceSystem) : i.tree.average = i.initial :=
  roundResources_average _ _ _ _

noncomputable def law (i : NestedResourceSystem) : Mixed 3 := i.tree.eval i.leafLaw

theorem leafLaw_contract (i : NestedResourceSystem) (r : Allocation 3) (hr : i.Valid r) :
    (∀ᵐ x ∂(i.leafLaw r : Measure (Allocation 3)), FullBudget i.M x) ∧
      ∀ j, (marginal (i.leafLaw r) j : Measure ℝ) = affineMeasure (r j / i.capacity j)
        (uniformLaw (i.short j)) (uniformLaw (i.long j)) := by
  classical
  rw [leafLaw, dite_eq_left hr]
  exact (i.terminal r hr).law_contract

theorem law_contract (i : NestedResourceSystem) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 3)), FullBudget i.M x) ∧
      ∀ j, (marginal i.law j : Measure ℝ) = affineMeasure (i.initialWeight j)
        (uniformLaw (i.short j)) (uniformLaw (i.long j)) := by
  constructor
  · apply i.tree.eval_fullBudget
    exact i.tree.forLeaves_mono (fun r hr => (i.leafLaw_contract r hr).1) i.tree_valid
  · intro j
    have hbox : i.tree.ForLeaves (InBox i.capacity) :=
      i.tree.forLeaves_mono (fun _ hr => hr.1) i.tree_valid
    have hm := i.tree.forLeaves_mono (fun r hr => (i.leafLaw_contract r hr).2 j) i.tree_valid
    have he := i.tree.eval_affine_marginal i.leafLaw i.capacity
      (fun j => sub_pos.mpr (i.short_lt j)) j j (uniformLaw (i.short j)) (uniformLaw (i.long j)) hbox hm
    simpa only [i.tree_average, law, initialWeight] using he

theorem law_inBox (i : NestedResourceSystem) : ∀ᵐ x ∂(i.law : Measure (Allocation 3)), InBox i.long x := by
  apply law_inBox_of_marginals
  intro j
  rw [i.law_contract.2 j]
  exact affineMeasure_supported (le_of_lt (i.short_lt j)) _

noncomputable def point (i : NestedResourceSystem) (choice : ℕ → Bool) (useFamily : Bool)
    (r t : ℝ) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 3 := by
  classical
  let resource := i.tree.traceLeaf choice
  exact if hr : i.Valid resource then (i.terminal resource hr).point useFamily r t edge residualEdge else 0

theorem point_contract (i : NestedResourceSystem) (choice : ℕ → Bool) (useFamily : Bool)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.M (i.point choice useFamily r t edge residualEdge) ∧
      InBox i.long (i.point choice useFamily r t edge residualEdge) := by
  classical
  have hv := i.tree.trace_forLeaves i.Valid i.tree_valid choice
  rw [point, dite_eq_left hv]
  exact ⟨(i.terminal _ hv).point_fullBudget useFamily hr ht edge residualEdge,
    (i.terminal _ hv).point_inBox useFamily hr ht edge residualEdge⟩

end NestedResourceSystem
end Blotto
