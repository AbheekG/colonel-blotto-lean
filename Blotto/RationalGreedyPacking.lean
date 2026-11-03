import Blotto.GreedyPacking
import Blotto.RationalActiveResources

/-! Native rational next-fit grouping. The real interpretation is exactly
the maintained original-order scan, including its cached current total. -/

namespace Blotto

def rationalGroupLength {α : Type*} (L : α → ℚ) (items : List α) : ℚ := (items.map L).sum

def rationalPackAux {α : Type*} (L : α → ℚ) (B : ℚ) : List α → ℚ → List α → List (List α)
  | current, _s, [] => [current.reverse]
  | current, s, x :: rest =>
    if s + L x ≤ B then rationalPackAux L B (x :: current) (s + L x) rest
    else current.reverse :: rationalPackAux L B [x] (L x) rest

def rationalGreedyGroups {α : Type*} (L : α → ℚ) (B : ℚ) : List α → List (List α)
  | [] => []
  | x :: rest => rationalPackAux L B [x] (L x) rest

theorem rationalGroupLength_real {α : Type*} (L : α → ℚ) (items : List α) :
    (rationalGroupLength L items : ℝ) = groupLength (fun x => (L x : ℝ)) items := by
  induction items with
  | nil => simp [rationalGroupLength, groupLength]
  | cons x xs ih =>
    simp only [rationalGroupLength, groupLength, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    rw [ih]

theorem rationalPackAux_real {α : Type*} (L : α → ℚ) (B : ℚ) (current : List α) (s : ℚ) (rest : List α) :
    rationalPackAux L B current s rest = packAux (fun x => (L x : ℝ)) B current s rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    have he : s + L x ≤ B ↔ (s : ℝ) + (L x : ℝ) ≤ (B : ℝ) := by norm_cast
    unfold rationalPackAux packAux
    by_cases hf : s + L x ≤ B
    · rw [ite_eq_left hf, ite_eq_left (he.mp hf)]
      simpa only [Rat.cast_add] using ih (x :: current) (s + L x)
    · rw [ite_eq_right hf, ite_eq_right (fun h => hf (he.mpr h))]
      rw [ih]

theorem rationalGreedyGroups_real {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α) :
    rationalGreedyGroups L B items = greedyGroups (fun x => (L x : ℝ)) B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact rationalPackAux_real L B [x] (L x) rest

theorem rationalGreedyGroups_flatten {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α) :
    (rationalGreedyGroups L B items).flatten = items := by
  rw [rationalGreedyGroups_real]
  exact greedyGroups_flatten _ _ _

theorem rationalGreedyGroups_bounds {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α)
    (h : ∀ x ∈ items, 0 < L x ∧ L x ≤ B) :
    ∀ group ∈ rationalGreedyGroups L B items, group ≠ [] ∧ 0 < rationalGroupLength L group ∧ rationalGroupLength L group ≤ B := by
  rw [rationalGreedyGroups_real]
  have hr : ∀ x ∈ items, (0 : ℝ) < L x ∧ (L x : ℝ) ≤ B := by
    intro x hx
    exact_mod_cast h x hx
  intro group hg
  have he := greedyGroups_bounds (fun x => (L x : ℝ)) B items hr group hg
  have hp : (0 : ℝ) < rationalGroupLength L group ∧ (rationalGroupLength L group : ℝ) ≤ B := by
    rw [rationalGroupLength_real]
    exact he.2
  exact ⟨he.1, by exact_mod_cast hp⟩

theorem rationalGreedyGroups_count {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α)
    (h : ∀ x ∈ items, 0 < L x ∧ L x ≤ B) (hs : rationalGroupLength L items ≤ 2 * B) :
    (rationalGreedyGroups L B items).length ≤ 3 := by
  rw [rationalGreedyGroups_real]
  have hr : ∀ x ∈ items, (0 : ℝ) < L x ∧ (L x : ℝ) ≤ B := by
    intro x hx
    exact_mod_cast h x hx
  have hm : groupLength (fun x => (L x : ℝ)) items ≤ 2 * (B : ℝ) := by
    rw [← rationalGroupLength_real]
    exact_mod_cast hs
  exact greedyGroups_count _ _ _ hr hm

def saturatedResourceItems {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (s.resource.allocation j = L j))

theorem saturatedResourceItems_real {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    saturatedResourceItems s = (List.finRange n).filter (fun j => decide (s.resource.realAllocation j = (L j : ℝ))) := by
  classical
  unfold saturatedResourceItems
  congr 1
  funext j
  simp only [RationalResourceArray.realAllocation, Rat.cast_inj]

end Blotto
