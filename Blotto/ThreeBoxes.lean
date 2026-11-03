import Blotto.Boxes
import Blotto.UnorderedThree

/-! Every three-variable output path stays inside its marginal coordinate box. -/

namespace Blotto
open MeasureTheory Set

namespace ThreeInput

theorem couplingPoint_inBox (i : ThreeInput) (edge : Fin 9) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : InBox ![i.a, i.d, i.c] (i.couplingPoint edge t) := by
  unfold couplingPoint
  split_ifs with he
  · have hm := i.geometry_matches he
    simpa only [hm.1, hm.2.1, hm.2.2.1] using (i.geometry he).couplingPoint_inBox edge ht
  · have hE := le_antisymm (le_of_not_gt he) i.E_nonnegative
    have hc := (i.exceptional_case hE).2.1
    intro j
    fin_cases j
    · change 0 ≤ i.a * t ∧ i.a * t ≤ i.a
      exact ⟨mul_nonneg (le_of_lt i.a_pos) ht.1, by nlinarith [i.a_pos]⟩
    · change 0 ≤ i.d * t ∧ i.d * t ≤ i.d
      exact ⟨mul_nonneg (le_of_lt i.d_pos) ht.1, by nlinarith [i.d_pos]⟩
    · change 0 ≤ i.B * (1 - t) ∧ i.B * (1 - t) ≤ i.c
      rw [hc]
      exact ⟨mul_nonneg (le_of_lt i.B_pos) (sub_nonneg.mpr ht.2), by nlinarith [i.B_pos]⟩

end ThreeInput

namespace ThreeSpec

theorem point_inBox (i : ThreeSpec) (edge : Fin 9) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.point edge t) := by
  have hb := i.orderedInput.couplingPoint_inBox edge ht
  unfold point
  split_ifs with had
  · simpa [orderedInput, min_eq_left had, max_eq_right had] using hb
  · have hda := le_of_lt (lt_of_not_ge had)
    intro j
    fin_cases j
    · simpa [swapFirst, orderedInput, max_eq_left hda] using hb 1
    · simpa [swapFirst, orderedInput, min_eq_right hda] using hb 0
    · simpa [swapFirst, orderedInput] using hb 2

end ThreeSpec
end Blotto
