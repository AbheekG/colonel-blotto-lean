import Blotto.ThreePoint

/-! Explicit three-variable laws and output paths with no ordering restriction
on the first two lengths. One coordinate swap performs the normalization. -/

namespace Blotto
open MeasureTheory Set

structure ThreeSpec where
  B : ℝ
  a : ℝ
  d : ℝ
  c : ℝ
  p : ℝ
  B_pos : 0 < B
  a_pos : 0 < a
  d_pos : 0 < d
  c_pos : 0 < c
  p_pos : 0 < p
  a_le : a ≤ B
  d_le : d ≤ B
  c_le : c ≤ B
  p_le : p ≤ 1
  balance : a + d + p * c = 2 * B

namespace ThreeSpec

noncomputable def orderedInput (i : ThreeSpec) : ThreeInput where
  B := i.B
  a := min i.a i.d
  d := max i.a i.d
  c := i.c
  p := i.p
  B_pos := i.B_pos
  a_pos := lt_min i.a_pos i.d_pos
  d_pos := lt_of_lt_of_le i.a_pos (le_max_left _ _)
  c_pos := i.c_pos
  p_pos := i.p_pos
  a_le := le_trans (min_le_left _ _) i.a_le
  d_le := max_le i.a_le i.d_le
  c_le := i.c_le
  p_le := i.p_le
  ordered := min_le_max
  balance := by rw [min_add_max]; exact i.balance

noncomputable def law (i : ThreeSpec) : Mixed 3 :=
  if i.a ≤ i.d then i.orderedInput.couplingLaw else swapLaw i.orderedInput.couplingLaw

theorem law_contract (i : ThreeSpec) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 3)), FullBudget i.B x) ∧
      (marginal i.law 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal i.law 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal i.law 2 : Measure ℝ) = zeroUniformLaw i.c i.p := by
  have hb := i.orderedInput.couplingLaw_fullBudget
  have hm := i.orderedInput.couplingLaw_marginals
  unfold law
  split_ifs with had
  · refine ⟨hb, ?_, ?_, hm.2.2⟩
    · rw [hm.1]
      change uniformLaw (min i.a i.d) = _
      rw [min_eq_left had]
    · rw [hm.2.1]
      change uniformLaw (max i.a i.d) = _
      rw [max_eq_right had]
  · have hda := le_of_lt (lt_of_not_ge had)
    refine ⟨swapLaw_fullBudget hb, ?_, ?_, ?_⟩
    · rw [swapLaw_marginal]
      change (marginal i.orderedInput.couplingLaw 1 : Measure ℝ) = _
      rw [hm.2.1]
      change uniformLaw (max i.a i.d) = _
      rw [max_eq_left hda]
    · rw [swapLaw_marginal]
      change (marginal i.orderedInput.couplingLaw 0 : Measure ℝ) = _
      rw [hm.1]
      change uniformLaw (min i.a i.d) = _
      rw [min_eq_right hda]
    · rw [swapLaw_marginal]
      exact hm.2.2

noncomputable def point (i : ThreeSpec) (edge : Fin 9) (t : ℝ) : Allocation 3 :=
  if i.a ≤ i.d then i.orderedInput.couplingPoint edge t else swapFirst (i.orderedInput.couplingPoint edge t)

theorem point_fullBudget (i : ThreeSpec) (edge : Fin 9) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget i.B (i.point edge t) := by
  unfold point
  split_ifs
  · exact i.orderedInput.couplingPoint_fullBudget edge ht
  · exact swapFirst_fullBudget (i.orderedInput.couplingPoint_fullBudget edge ht)

end ThreeSpec
end Blotto
