import Blotto.NestedBoxes
import Blotto.AffineMixture

/-! Explicit ordered-or-swapped nested laws with endpoint mixture weights.
Both interval lengths stay positive, as in the reflected four-variable branch. -/

namespace Blotto
open MeasureTheory Set

structure NestedSpec where
  M : ℝ
  a : ℝ
  d : ℝ
  c : ℝ
  t : ℝ
  q : ℝ
  a_pos : 0 < a
  d_pos : 0 < d
  c_pos : 0 < c
  t_pos : 0 < t
  t_lt : t < c
  q_nonneg : 0 ≤ q
  q_le : q ≤ 1
  a_le : a ≤ M
  d_le : d ≤ M
  c_le : c ≤ M
  balance : a + d + q * t + (1 - q) * c = 2 * M

namespace NestedSpec

noncomputable def longInput (i : NestedSpec) (hq : i.q = 0) : ThreeSpec where
  B := i.M
  a := i.a
  d := i.d
  c := i.c
  p := 1
  B_pos := lt_of_lt_of_le i.a_pos i.a_le
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.c_pos
  p_pos := by norm_num
  a_le := i.a_le
  d_le := i.d_le
  c_le := i.c_le
  p_le := le_rfl
  balance := by simpa [hq] using i.balance

noncomputable def shortInput (i : NestedSpec) (hq : i.q = 1) : ThreeSpec where
  B := i.M
  a := i.a
  d := i.d
  c := i.t
  p := 1
  B_pos := lt_of_lt_of_le i.a_pos i.a_le
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.t_pos
  p_pos := by norm_num
  a_le := i.a_le
  d_le := i.d_le
  c_le := le_trans (le_of_lt i.t_lt) i.c_le
  p_le := le_rfl
  balance := by simpa [hq] using i.balance

noncomputable def interiorInput (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) : NestedInput where
  M := i.M
  a := min i.a i.d
  d := max i.a i.d
  c := i.c
  t := i.t
  q := i.q
  a_pos := lt_min i.a_pos i.d_pos
  d_pos := lt_of_lt_of_le i.a_pos (le_max_left _ _)
  c_pos := i.c_pos
  t_pos := i.t_pos
  t_lt := i.t_lt
  q_pos := hq0
  q_lt := hq1
  a_le := le_trans (min_le_left _ _) i.a_le
  d_le := max_le i.a_le i.d_le
  c_le := i.c_le
  ordered := min_le_max
  balance := by rw [min_add_max]; exact i.balance

noncomputable def law (i : NestedSpec) : Mixed 3 :=
  if hq0 : i.q = 0 then (i.longInput hq0).law else
    if hq1 : i.q = 1 then (i.shortInput hq1).law else
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      if i.a ≤ i.d then j.couplingLaw else swapLaw j.couplingLaw

theorem law_contract (i : NestedSpec) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal i.law 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal i.law 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal i.law 2 : Measure ℝ) = affineMeasure i.q (uniformLaw i.t) (uniformLaw i.c) := by
  unfold law
  split_ifs with hq0 hq1 had
  · have h := (i.longInput hq0).law_contract
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    simpa [longInput, zeroUniformLaw, affineMeasure, hq0] using h.2.2.2
  · have h := (i.shortInput hq1).law_contract
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    simpa [shortInput, zeroUniformLaw, affineMeasure, hq1] using h.2.2.2
  · have h := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).coupling_contract
    refine ⟨h.1, ?_, ?_, ?_⟩
    · simpa [interiorInput, min_eq_left had] using h.2.1
    · simpa [interiorInput, max_eq_right had] using h.2.2.1
    · simpa [interiorInput, NestedInput.nestedTargetLaw, affineMeasure] using h.2.2.2
  · have hda := le_of_lt (lt_of_not_ge had)
    have h := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).coupling_contract
    refine ⟨swapLaw_fullBudget h.1, ?_, ?_, ?_⟩
    · rw [swapLaw_marginal]
      simpa [swapIndex, interiorInput, max_eq_left hda] using h.2.2.1
    · rw [swapLaw_marginal]
      simpa [swapIndex, interiorInput, min_eq_right hda] using h.2.1
    · rw [swapLaw_marginal]
      simpa [swapIndex, interiorInput, NestedInput.nestedTargetLaw, affineMeasure] using h.2.2.2

noncomputable def point (i : NestedSpec) (useFamily : Bool) (r t : ℝ)
    (edge : Fin 9) (residualEdge : Fin 3) : Allocation 3 :=
  if hq0 : i.q = 0 then (i.longInput hq0).point edge t else
    if hq1 : i.q = 1 then (i.shortInput hq1).point edge t else
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      if i.a ≤ i.d then j.couplingPoint useFamily r t edge residualEdge else
        swapFirst (j.couplingPoint useFamily r t edge residualEdge)

theorem point_fullBudget (i : NestedSpec) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.M (i.point useFamily r t edge residualEdge) := by
  unfold point
  split_ifs
  · exact (i.longInput _).point_fullBudget edge ht
  · exact (i.shortInput _).point_fullBudget edge ht
  · exact (i.interiorInput _ _).couplingPoint_fullBudget useFamily hr ht edge residualEdge
  · exact swapFirst_fullBudget ((i.interiorInput _ _).couplingPoint_fullBudget useFamily hr ht edge residualEdge)

theorem point_inBox (i : NestedSpec) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    InBox ![i.a, i.d, i.c] (i.point useFamily r t edge residualEdge) := by
  unfold point
  split_ifs with hq0 hq1 had
  · exact (i.longInput hq0).point_inBox edge ht
  · have hb := (i.shortInput hq1).point_inBox edge ht
    apply inBox_mono _ hb
    intro j
    fin_cases j
    · exact le_rfl
    · exact le_rfl
    · exact le_of_lt i.t_lt
  · have hb := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
      (lt_of_le_of_ne i.q_le hq1)).couplingPoint_inBox useFamily hr ht edge residualEdge
    simpa [interiorInput, min_eq_left had, max_eq_right had] using hb
  · have hda := le_of_lt (lt_of_not_ge had)
    have hb := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
      (lt_of_le_of_ne i.q_le hq1)).couplingPoint_inBox useFamily hr ht edge residualEdge
    intro j
    fin_cases j
    · simpa [swapFirst, interiorInput, max_eq_left hda] using hb 1
    · simpa [swapFirst, interiorInput, min_eq_right hda] using hb 0
    · simpa [swapFirst, interiorInput] using hb 2

end NestedSpec
end Blotto
