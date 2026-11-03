import Blotto.ThreeCoupling

/-! Pointwise output path of the three-variable sampler, including E=0. -/

namespace Blotto.ThreeInput
open MeasureTheory Set

noncomputable def couplingPoint (i : ThreeInput) (edge : Fin 9) (t : ℝ) : Allocation 3 :=
  if he : 0 < i.a + i.d - i.B then (i.geometry he).couplingPoint edge t
    else ![i.a * t, i.d * t, i.B * (1 - t)]

theorem couplingPoint_fullBudget (i : ThreeInput) (edge : Fin 9) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : FullBudget i.B (i.couplingPoint edge t) := by
  unfold couplingPoint
  split_ifs with he
  · have hB := (i.geometry_matches he).2.2.2.1
    simpa only [hB] using (i.geometry he).couplingPoint_fullBudget edge ht
  · have hE := le_antisymm (le_of_not_gt he) i.E_nonnegative
    exact three_exceptional_budget (le_of_lt i.a_pos) (le_of_lt i.d_pos) (le_of_lt i.B_pos)
      (i.exceptional_case hE).2.2 ht

end Blotto.ThreeInput
