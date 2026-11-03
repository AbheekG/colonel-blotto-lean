import Blotto.FiniteMixture
import Blotto.ThreeWeights
import Blotto.ThreeDensities
import Blotto.WeightedIntervals

/-! The finite whole-allocation lotteries specified by all three weight tables.
The marginal identities are proved separately from hard-budget feasibility. -/

namespace Blotto

open MeasureTheory Set Filter
open scoped BigOperators

namespace SegmentWeights

noncomputable def vector (q : SegmentWeights) : Fin 9 → ℝ :=
  ![q.q13, q.q14, q.q15, q.q24, q.q25, q.q26, q.q36, q.q45, q.q46]

theorem vector_mass (q : SegmentWeights) : ∑ i, q.vector i = q.mass := by
  simp [vector, mass, Fin.sum_univ_succ]
  ring

theorem vector_nonnegative (q : SegmentWeights) (hq : q.Nonnegative) : ∀ i, 0 ≤ q.vector i := by
  rcases hq with ⟨h13, h14, h15, h24, h25, h26, h36, h45, h46⟩
  intro i
  fin_cases i
  · exact h13
  · exact h14
  · exact h15
  · exact h24
  · exact h25
  · exact h26
  · exact h36
  · exact h45
  · exact h46

end SegmentWeights

noncomputable def threeEdges : Fin 9 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (2, 5), (3, 4), (3, 5)]

namespace ThreeGeometry

noncomputable def edgeLaw (g : ThreeGeometry) (i : Fin 9) : Mixed 3 :=
  segmentLaw (g.vertex (threeEdges i).1) (g.vertex (threeEdges i).2)

noncomputable def tableLaw (g : ThreeGeometry) (q : SegmentWeights)
    (hq : q.Nonnegative) (hm : q.mass = 1) : Mixed 3 :=
  probabilityMixture q.vector g.edgeLaw (q.vector_nonnegative hq) (by rw [q.vector_mass, hm])

theorem tableLaw_supported (g : ThreeGeometry) (q : SegmentWeights)
    (hq : q.Nonnegative) (hm : q.mass = 1) : Supported g.budget (g.tableLaw q hq hm) := by
  apply probabilityMixture_supported
  intro i
  exact g.vertex_segment_supported _ _

theorem tableLaw_fullBudget (g : ThreeGeometry) (q : SegmentWeights)
    (hq : q.Nonnegative) (hm : q.mass = 1) :
    ∀ᵐ x ∂(g.tableLaw q hq hm : Measure (Allocation 3)), FullBudget g.budget x := by
  apply probabilityMixture_ae
  intro i
  exact segmentLaw_fullBudget (g.vertex_fullBudget _) (g.vertex_fullBudget _)

noncomputable def chosenWeights (g : ThreeGeometry) : SegmentWeights :=
  if g.w ≤ g.v then g.firstWeights else if g.w ≤ g.u then g.secondWeights else g.thirdWeights

theorem chosenWeights_nonnegative (g : ThreeGeometry) : g.chosenWeights.Nonnegative := by
  unfold chosenWeights
  split_ifs with h1 h2
  · exact g.firstWeights_nonnegative h1
  · exact g.secondWeights_nonnegative h2
  · exact g.thirdWeights_nonnegative (le_of_lt (lt_of_not_ge h2))

theorem chosenWeights_mass (g : ThreeGeometry) : g.chosenWeights.mass = 1 := by
  unfold chosenWeights
  split_ifs
  · exact g.firstWeights_mass
  · exact g.secondWeights_mass
  · exact g.thirdWeights_mass

noncomputable def couplingLaw (g : ThreeGeometry) : Mixed 3 :=
  g.tableLaw g.chosenWeights g.chosenWeights_nonnegative g.chosenWeights_mass

theorem couplingLaw_fullBudget (g : ThreeGeometry) :
    ∀ᵐ x ∂(g.couplingLaw : Measure (Allocation 3)), FullBudget g.budget x :=
  g.tableLaw_fullBudget _ _ _

theorem tableLaw_marginal (g : ThreeGeometry) (q : SegmentWeights)
    (hq : q.Nonnegative) (hm : q.mass = 1) (j : Fin 3) :
    (marginal (g.tableLaw q hq hm) j : Measure ℝ) =
      ∑ i, ENNReal.ofReal (q.vector i) •
        (affineUniform (g.vertex (threeEdges i).1 j) (g.vertex (threeEdges i).2 j) : Measure ℝ) := by
  rw [tableLaw, probabilityMixture_marginal]
  simp only [Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [edgeLaw, segmentLaw_marginal]

/-- Slots that may carry positive mass in the selected table. -/
noncomputable def enabledEdges (g : ThreeGeometry) : Finset (Fin 9) :=
  if g.w ≤ g.v then {0, 1, 4, 5, 6, 7, 8}
  else if g.w ≤ g.u then {0, 1, 2, 6, 7, 8}
  else {1, 2, 3, 4, 7}

theorem enabledEdges_card (g : ThreeGeometry) : g.enabledEdges.card ≤ 7 := by
  unfold enabledEdges
  split_ifs <;> norm_num

theorem chosenWeights_zero_outside (g : ThreeGeometry) (i : Fin 9)
    (hi : i ∉ g.enabledEdges) : g.chosenWeights.vector i = 0 := by
  unfold enabledEdges at hi
  unfold chosenWeights
  split_ifs with h1 h2
  · fin_cases i <;> simp [SegmentWeights.vector, firstWeights, h1] at *
  · fin_cases i <;> simp [SegmentWeights.vector, secondWeights, h1, h2] at *
  · fin_cases i <;> simp [SegmentWeights.vector, thirdWeights, h1, h2] at *

theorem positiveEdges_card (g : ThreeGeometry) :
    (Finset.univ.filter fun i => 0 < g.chosenWeights.vector i).card ≤ 7 := by
  classical
  apply le_trans (Finset.card_le_card ?_) g.enabledEdges_card
  intro i hi
  by_contra hn
  have hz := g.chosenWeights_zero_outside i hn
  have hp := (Finset.mem_filter.mp hi).2
  rw [hz] at hp
  exact lt_irrefl 0 hp

end ThreeGeometry
end Blotto
