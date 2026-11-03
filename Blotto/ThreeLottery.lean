import Blotto.LotteryTransform
import Blotto.ThreeBoxes

/-! Concrete finite segment descriptions of all three-variable laws, with
at most seven positive entries and feasibility of all descriptor endpoints. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

namespace ThreeGeometry

noncomputable def segmentLottery (g : ThreeGeometry) : SegmentLottery 3 9 :=
  ⟨g.chosenWeights.vector, (fun i => g.vertex (threeEdges i).1), (fun i => g.vertex (threeEdges i).2),
    g.chosenWeights.vector_nonnegative g.chosenWeights_nonnegative,
    by rw [g.chosenWeights.vector_mass, g.chosenWeights_mass]⟩

theorem segmentLottery_law (g : ThreeGeometry) :
    (g.segmentLottery.law : Measure (Allocation 3)) = (g.couplingLaw : Measure (Allocation 3)) := rfl

theorem segmentLottery_positive (g : ThreeGeometry) : g.segmentLottery.positiveSlots.card ≤ 7 :=
  g.positiveEdges_card

theorem segmentLottery_endpoints (g : ThreeGeometry) :
    (∀ i, FullBudget g.budget (g.segmentLottery.P i)) ∧
      (∀ i, FullBudget g.budget (g.segmentLottery.Q i)) :=
  ⟨fun _ => g.vertex_fullBudget _, fun _ => g.vertex_fullBudget _⟩

theorem segmentLottery_box (g : ThreeGeometry) :
    (∀ i, InBox ![g.a, g.d, g.c] (g.segmentLottery.P i)) ∧
      (∀ i, InBox ![g.a, g.d, g.c] (g.segmentLottery.Q i)) :=
  ⟨fun _ => g.vertex_inBox _, fun _ => g.vertex_inBox _⟩

end ThreeGeometry

namespace ThreeInput

noncomputable def segmentLottery (i : ThreeInput) : SegmentLottery 3 9 :=
  if he : 0 < i.a + i.d - i.B then (i.geometry he).segmentLottery else
    ⟨(fun j => if j = 0 then 1 else 0), (fun _ => ![0, 0, i.B]), (fun _ => ![i.a, i.d, 0]),
      (by intro j; split_ifs <;> norm_num), (by simp)⟩

theorem segmentLottery_law (i : ThreeInput) :
    (i.segmentLottery.law : Measure (Allocation 3)) = (i.couplingLaw : Measure (Allocation 3)) := by
  unfold segmentLottery couplingLaw
  split_ifs with he
  · exact (i.geometry he).segmentLottery_law
  · simp [SegmentLottery.law, probabilityMixture, mixtureMeasure, Measure.sum_fintype,
      Fin.sum_univ_succ, exceptionalLaw]

theorem segmentLottery_positive (i : ThreeInput) : i.segmentLottery.positiveSlots.card ≤ 7 := by
  classical
  unfold segmentLottery
  split_ifs with he
  · exact (i.geometry he).segmentLottery_positive
  · change (Finset.univ.filter (fun j : Fin 9 => 0 < (if j = 0 then (1 : ℝ) else 0))).card ≤ 7
    have hset : Finset.univ.filter (fun j : Fin 9 => 0 < (if j = 0 then (1 : ℝ) else 0)) = {0} := by
      ext j
      by_cases hj : j = 0 <;> simp [hj]
    rw [hset]
    norm_num

theorem segmentLottery_endpoints (i : ThreeInput) :
    (∀ j, FullBudget i.B (i.segmentLottery.P j)) ∧ (∀ j, FullBudget i.B (i.segmentLottery.Q j)) := by
  unfold segmentLottery
  split_ifs with he
  · have hB := (i.geometry_matches he).2.2.2.1
    simpa only [hB] using (i.geometry he).segmentLottery_endpoints
  · have hE := le_antisymm (le_of_not_gt he) i.E_nonnegative
    have heq := (i.exceptional_case hE).2.2
    constructor
    · intro j
      exact fullBudget_three (le_rfl) (le_rfl) (le_of_lt i.B_pos) (by ring)
    · intro j
      exact fullBudget_three (le_of_lt i.a_pos) (le_of_lt i.d_pos) le_rfl (by linarith)

theorem segmentLottery_box (i : ThreeInput) :
    (∀ j, InBox ![i.a, i.d, i.c] (i.segmentLottery.P j)) ∧
      (∀ j, InBox ![i.a, i.d, i.c] (i.segmentLottery.Q j)) := by
  unfold segmentLottery
  split_ifs with he
  · have hm := i.geometry_matches he
    simpa only [hm.1, hm.2.1, hm.2.2.1] using (i.geometry he).segmentLottery_box
  · have hE := le_antisymm (le_of_not_gt he) i.E_nonnegative
    have hc := (i.exceptional_case hE).2.1
    constructor
    · intro j k
      fin_cases k
      · exact ⟨le_rfl, le_of_lt i.a_pos⟩
      · exact ⟨le_rfl, le_of_lt i.d_pos⟩
      · change 0 ≤ i.B ∧ i.B ≤ i.c
        exact ⟨le_of_lt i.B_pos, le_of_eq hc.symm⟩
    · intro j k
      fin_cases k
      · exact ⟨le_of_lt i.a_pos, le_rfl⟩
      · exact ⟨le_of_lt i.d_pos, le_rfl⟩
      · exact ⟨le_rfl, le_of_lt i.c_pos⟩

end ThreeInput

namespace ThreeSpec

noncomputable def segmentLottery (i : ThreeSpec) : SegmentLottery 3 9 :=
  if i.a ≤ i.d then i.orderedInput.segmentLottery else i.orderedInput.segmentLottery.mapped AffineAllocation.swapFirst

theorem segmentLottery_law (i : ThreeSpec) :
    (i.segmentLottery.law : Measure (Allocation 3)) = (i.law : Measure (Allocation 3)) := by
  unfold segmentLottery law
  split_ifs with h
  · exact i.orderedInput.segmentLottery_law
  · rw [SegmentLottery.mapped_law, i.orderedInput.segmentLottery_law]
    rfl

theorem segmentLottery_positive (i : ThreeSpec) : i.segmentLottery.positiveSlots.card ≤ 7 := by
  unfold segmentLottery
  split_ifs
  · exact i.orderedInput.segmentLottery_positive
  · exact i.orderedInput.segmentLottery_positive

theorem segmentLottery_endpoints (i : ThreeSpec) :
    (∀ j, FullBudget i.B (i.segmentLottery.P j)) ∧ (∀ j, FullBudget i.B (i.segmentLottery.Q j)) := by
  have he := i.orderedInput.segmentLottery_endpoints
  unfold segmentLottery
  split_ifs
  · exact he
  · exact ⟨fun j => swapFirst_fullBudget (he.1 j), fun j => swapFirst_fullBudget (he.2 j)⟩

theorem segmentLottery_box (i : ThreeSpec) :
    (∀ j, InBox ![i.a, i.d, i.c] (i.segmentLottery.P j)) ∧
      (∀ j, InBox ![i.a, i.d, i.c] (i.segmentLottery.Q j)) := by
  have he := i.orderedInput.segmentLottery_box
  unfold segmentLottery
  split_ifs with had
  · simpa [orderedInput, min_eq_left had, max_eq_right had] using he
  · have hda := le_of_lt (lt_of_not_ge had)
    constructor
    · intro j k
      fin_cases k
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput, max_eq_left hda] using he.1 j 1
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput, min_eq_right hda] using he.1 j 0
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput] using he.1 j 2
    · intro j k
      fin_cases k
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput, max_eq_left hda] using he.2 j 1
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput, min_eq_right hda] using he.2 j 0
      · simpa [SegmentLottery.mapped, AffineAllocation.swapFirst, swapFirst, orderedInput] using he.2 j 2

end ThreeSpec
end Blotto
