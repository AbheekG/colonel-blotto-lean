import Blotto.RationalGreedyPacking

/-! The executable next-fit scan retains each group's sum when closing it.
Each item's length and tentative sum are evaluated once. The raw lists and
stored sums refine the retained mathematical greedy partition exactly. -/

namespace Blotto

def rationalPackSumsAux {α : Type*} (L : α → ℚ) (B : ℚ) :
    List α → ℚ → List α → List (List α × ℚ)
  | current, s, [] => [(current.reverse, s)]
  | current, s, x :: rest =>
    let itemLength := L x
    let next := s + itemLength
    if next ≤ B then rationalPackSumsAux L B (x :: current) next rest
    else (current.reverse, s) :: rationalPackSumsAux L B [x] itemLength rest

def rationalPackedGroups {α : Type*} (L : α → ℚ) (B : ℚ) : List α → List (List α × ℚ)
  | [] => []
  | x :: rest => rationalPackSumsAux L B [x] (L x) rest

theorem rationalPackSumsAux_groups {α : Type*} (L : α → ℚ) (B : ℚ)
    (current : List α) (s : ℚ) (rest : List α) :
    (rationalPackSumsAux L B current s rest).map Prod.fst = rationalPackAux L B current s rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    rw [rationalPackSumsAux, rationalPackAux]
    split_ifs
    · exact ih _ _
    · simp only [List.map_cons]
      rw [ih]

theorem rationalPackSumsAux_totals {α : Type*} (L : α → ℚ) (B : ℚ)
    (current : List α) (s : ℚ) (rest : List α) (hs : rationalGroupLength L current = s) :
    ∀ entry ∈ rationalPackSumsAux L B current s rest, entry.2 = rationalGroupLength L entry.1 := by
  induction rest generalizing current s with
  | nil =>
    intro entry he
    have hEntry : entry = (current.reverse, s) := by simpa only [rationalPackSumsAux, List.mem_singleton] using he
    subst entry
    exact (show rationalGroupLength L current.reverse = rationalGroupLength L current from by simp [rationalGroupLength, List.map_reverse]).trans hs |>.symm
  | cons x rest ih =>
    rw [rationalPackSumsAux]
    split_ifs
    · exact ih (x :: current) (s + L x) (by simp only [rationalGroupLength, List.map_cons, List.sum_cons] at hs ⊢; rw [hs]; ring)
    · intro entry he
      rcases List.mem_cons.mp he with hEntry | he
      · subst entry
        exact (show rationalGroupLength L current.reverse = rationalGroupLength L current from by simp [rationalGroupLength, List.map_reverse]).trans hs |>.symm
      · exact ih [x] (L x) (by simp [rationalGroupLength]) entry he

theorem rationalPackedGroups_groups {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α) :
    (rationalPackedGroups L B items).map Prod.fst = rationalGreedyGroups L B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact rationalPackSumsAux_groups L B [x] (L x) rest

theorem rationalPackedGroups_totals {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α) :
    ∀ entry ∈ rationalPackedGroups L B items, entry.2 = rationalGroupLength L entry.1 := by
  cases items with
  | nil => simp [rationalPackedGroups]
  | cons x rest => exact rationalPackSumsAux_totals L B [x] (L x) rest (by simp [rationalGroupLength])

end Blotto
