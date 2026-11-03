import Blotto.GreedyPacking

/-! The executable next-fit scan retains each group's sum when closing it.
Each item's length and tentative sum are evaluated once. The raw lists and
stored sums refine the retained mathematical greedy partition exactly. -/

namespace Blotto
open scoped Classical

noncomputable def realPackSumsAux {α : Type*} (L : α → ℝ) (B : ℝ) :
    List α → ℝ → List α → List (List α × ℝ)
  | current, s, [] => [(current.reverse, s)]
  | current, s, x :: rest =>
    let itemLength := L x
    let next := s + itemLength
    if next ≤ B then realPackSumsAux L B (x :: current) next rest
    else (current.reverse, s) :: realPackSumsAux L B [x] itemLength rest

noncomputable def realPackedGroups {α : Type*} (L : α → ℝ) (B : ℝ) : List α → List (List α × ℝ)
  | [] => []
  | x :: rest => realPackSumsAux L B [x] (L x) rest

theorem realPackSumsAux_groups {α : Type*} (L : α → ℝ) (B : ℝ)
    (current : List α) (s : ℝ) (rest : List α) :
    (realPackSumsAux L B current s rest).map Prod.fst = packAux L B current s rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    rw [realPackSumsAux, packAux]
    split_ifs
    · exact ih _ _
    · simp only [List.map_cons]
      rw [ih]

theorem realPackSumsAux_totals {α : Type*} (L : α → ℝ) (B : ℝ)
    (current : List α) (s : ℝ) (rest : List α) (hs : groupLength L current = s) :
    ∀ entry ∈ realPackSumsAux L B current s rest, entry.2 = groupLength L entry.1 := by
  induction rest generalizing current s with
  | nil =>
    intro entry he
    have hEntry : entry = (current.reverse, s) := by simpa only [realPackSumsAux, List.mem_singleton] using he
    subst entry
    exact (groupLength_reverse L current).trans hs |>.symm
  | cons x rest ih =>
    rw [realPackSumsAux]
    split_ifs
    · exact ih (x :: current) (s + L x) (by rw [groupLength_cons, hs]; ring)
    · intro entry he
      rcases List.mem_cons.mp he with hEntry | he
      · subst entry
        exact (groupLength_reverse L current).trans hs |>.symm
      · exact ih [x] (L x) (by simp [groupLength]) entry he

theorem realPackedGroups_groups {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α) :
    (realPackedGroups L B items).map Prod.fst = greedyGroups L B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact realPackSumsAux_groups L B [x] (L x) rest

theorem realPackedGroups_totals {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α) :
    ∀ entry ∈ realPackedGroups L B items, entry.2 = groupLength L entry.1 := by
  cases items with
  | nil => simp [realPackedGroups]
  | cons x rest => exact realPackSumsAux_totals L B [x] (L x) rest (by simp [groupLength])

end Blotto
