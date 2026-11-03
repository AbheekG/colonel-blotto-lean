import Blotto.TerminalLottoLaw
import Blotto.SmallGroupPaths

/-! Pathwise terminal feasibility survives grouping and proportional splitting. -/

namespace Blotto
open scoped BigOperators

namespace TerminalLotto

noncomputable def point {n : ℕ} (i : TerminalLotto n) (useUniform : Bool) (choice : ℕ → Bool)
    (useFamily : Bool) (r t : ℝ) (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation n := by
  classical
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · let pivot := h.choose
    let hp := (mem_fractionalSet _ _ _).mp h.choose_spec
    exact i.partition.splitMixed pivot ((i.mixedSpec pivot hp).point i.groups_count
      useUniform choice useFamily r t index edge residualEdge)
  · let hf := fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩
    exact i.partition.split ((i.uniformSpec hf).point i.groups_count edge t)

theorem point_fullBudget {n : ℕ} (i : TerminalLotto n) (useUniform : Bool) (choice : ℕ → Bool)
    (useFamily : Bool) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.point useUniform choice useFamily r t index edge residualEdge) := by
  unfold point
  split_ifs with h
  · apply i.partition.splitMixed_fullBudget
    exact (i.mixedSpec _ _).point_fullBudget i.groups_count useUniform choice useFamily hr ht index edge residualEdge
  · apply i.partition.split_fullBudget
    exact (i.uniformSpec _).point_fullBudget i.groups_count edge ht

end TerminalLotto
end Blotto
