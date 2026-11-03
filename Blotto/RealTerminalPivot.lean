import Blotto.TerminalLottoGrouping

/-! The terminal pivot is found by an explicit finite scan. Uniqueness
identifies it with the pivot used by the retained mathematical law. -/

namespace Blotto.TerminalLotto
open scoped Classical

noncomputable def realPivot {n : ℕ} (i : TerminalLotto n) : Option (Fin n) :=
  (List.finRange n).find? fun j => decide (Fractional i.length i.resource j)

theorem realPivot_none {n : ℕ} (i : TerminalLotto n) :
    i.realPivot = none ↔ ∀ j, ¬Fractional i.length i.resource j := by
  simp [realPivot, List.find?_eq_none]

theorem realPivot_some {n : ℕ} (i : TerminalLotto n) {j : Fin n} (h : i.realPivot = some j) :
    Fractional i.length i.resource j := by
  unfold realPivot at h
  have hp : decide (Fractional i.length i.resource j) = true :=
    List.find?_some (p := fun k : Fin n => decide (Fractional i.length i.resource k)) h
  exact of_decide_eq_true hp

theorem realPivot_eq_choose {n : ℕ} (i : TerminalLotto n) (h : (fractionalSet i.length i.resource).Nonempty) :
    i.realPivot = some h.choose := by
  cases hp : i.realPivot with
  | none =>
    exact False.elim ((i.realPivot_none.mp hp) h.choose ((mem_fractionalSet _ _ _).mp h.choose_spec))
  | some j =>
    have he := i.fractional_unique (i.realPivot_some hp) ((mem_fractionalSet _ _ _).mp h.choose_spec)
    exact congrArg some he

end Blotto.TerminalLotto
