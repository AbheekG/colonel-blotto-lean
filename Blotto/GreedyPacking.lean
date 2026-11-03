import Blotto.Rounding
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Forward next-fit grouping. The current group is stored in reverse order
with its cached length, so adding an item needs one sum/comparison and one cons.
Each closed group is reversed once when it is emitted. -/

namespace Blotto
open scoped BigOperators

noncomputable def groupLength {α : Type*} (L : α → ℝ) (g : List α) : ℝ := (g.map L).sum

noncomputable def packAux {α : Type*} (L : α → ℝ) (B : ℝ) : List α → ℝ → List α → List (List α)
  | current, _s, [] => [current.reverse]
  | current, s, x :: rest =>
    if s + L x ≤ B then packAux L B (x :: current) (s + L x) rest
    else current.reverse :: packAux L B [x] (L x) rest

noncomputable def greedyGroups {α : Type*} (L : α → ℝ) (B : ℝ) : List α → List (List α)
  | [] => []
  | x :: rest => packAux L B [x] (L x) rest

theorem packAux_flatten {α : Type*} (L : α → ℝ) (B : ℝ) (current : List α) (s : ℝ) (rest : List α) :
    (packAux L B current s rest).flatten = current.reverse ++ rest := by
  induction rest generalizing current s with
  | nil => simp [packAux]
  | cons x rest ih =>
    unfold packAux
    split_ifs
    · rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    · rw [List.flatten_cons, ih]
      simp

theorem greedyGroups_flatten {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α) :
    (greedyGroups L B items).flatten = items := by
  cases items with
  | nil => rfl
  | cons x rest => simpa [greedyGroups] using packAux_flatten L B [x] (L x) rest

theorem groupLength_nonnegative {α : Type*} (L : α → ℝ) (g : List α)
    (h : ∀ x ∈ g, 0 ≤ L x) : 0 ≤ groupLength L g := by
  apply List.sum_nonneg
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact h x hx

theorem groupLength_reverse {α : Type*} (L : α → ℝ) (g : List α) :
    groupLength L g.reverse = groupLength L g := by simp [groupLength, List.map_reverse]

theorem groupLength_cons {α : Type*} (L : α → ℝ) (x : α) (g : List α) :
    groupLength L (x :: g) = L x + groupLength L g := rfl

theorem groupLength_positive {α : Type*} (L : α → ℝ) (g : List α)
    (hne : g ≠ []) (h : ∀ x ∈ g, 0 < L x) : 0 < groupLength L g := by
  cases g with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    have hx := h x (by simp)
    have hsum := groupLength_nonnegative L xs (fun y hy => le_of_lt (h y (by simp [hy])))
    rw [groupLength_cons]
    linarith

theorem packAux_bounds {α : Type*} (L : α → ℝ) (B : ℝ) (current rest : List α) (s : ℝ)
    (hs : groupLength L current = s) (hsB : s ≤ B)
    (hcur : current ≠ []) (hC : ∀ x ∈ current, 0 < L x)
    (hrest : ∀ x ∈ rest, 0 < L x ∧ L x ≤ B) :
    ∀ g ∈ packAux L B current s rest, g ≠ [] ∧ 0 < groupLength L g ∧ groupLength L g ≤ B := by
  induction rest generalizing current s with
  | nil =>
    intro g hg
    have he : g = current.reverse := by simpa [packAux] using hg
    subst g
    rw [groupLength_reverse, hs]
    have hp := groupLength_positive L current hcur hC
    exact ⟨by simpa using hcur, by simpa [hs] using hp, hsB⟩
  | cons x rest ih =>
    have hx := hrest x (by simp)
    have hr : ∀ y ∈ rest, 0 < L y ∧ L y ≤ B := fun y hy => hrest y (by simp [hy])
    unfold packAux
    split_ifs with hfit
    · apply ih (x :: current) (s + L x)
      · rw [groupLength_cons, hs]; ring
      · exact hfit
      · simp
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx.1
        · exact hC y hy
      · exact hr
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · have hp := groupLength_positive L current hcur hC
        refine ⟨by simpa using hcur, ?_, ?_⟩
        · simpa only [groupLength_reverse] using hp
        · rw [groupLength_reverse, hs]; exact hsB
      · exact ih [x] (L x) (by simp [groupLength]) hx.2 (by simp)
          (by
            intro y hy
            have he : y = x := by simpa using hy
            subst y
            exact hx.1) hr g hg

def GroupsSeparated {α : Type*} (L : α → ℝ) (B : ℝ) : List (List α) → Prop
  | g :: h :: rest => B < groupLength L g + groupLength L h ∧ GroupsSeparated L B (h :: rest)
  | _ => True

theorem packAux_first_mass {α : Type*} (L : α → ℝ) (B : ℝ) (current rest : List α) (s : ℝ)
    (hs : groupLength L current = s) (hrest : ∀ x ∈ rest, 0 ≤ L x) :
    ∃ g gs, packAux L B current s rest = g :: gs ∧ s ≤ groupLength L g := by
  induction rest generalizing current s with
  | nil => exact ⟨current.reverse, [], rfl, by rw [groupLength_reverse, hs]⟩
  | cons x rest ih =>
    have hx := hrest x (by simp)
    have hr : ∀ y ∈ rest, 0 ≤ L y := fun y hy => hrest y (by simp [hy])
    unfold packAux
    split_ifs
    · have hn : groupLength L (x :: current) = s + L x := by rw [groupLength_cons, hs]; ring
      rcases ih (x :: current) (s + L x) hn hr with ⟨g, gs, he, hg⟩
      exact ⟨g, gs, he, le_trans (by linarith) hg⟩
    · exact ⟨current.reverse, packAux L B [x] (L x) rest, rfl, by rw [groupLength_reverse, hs]⟩

theorem packAux_separated {α : Type*} (L : α → ℝ) (B : ℝ) (current rest : List α) (s : ℝ)
    (hs : groupLength L current = s) (hrest : ∀ x ∈ rest, 0 ≤ L x) :
    GroupsSeparated L B (packAux L B current s rest) := by
  induction rest generalizing current s with
  | nil => trivial
  | cons x rest ih =>
    have hr : ∀ y ∈ rest, 0 ≤ L y := fun y hy => hrest y (by simp [hy])
    unfold packAux
    split_ifs with hfit
    · apply ih (x :: current) (s + L x) _ hr
      rw [groupLength_cons, hs]; ring
    · have hi := ih [x] (L x) (by simp [groupLength]) hr
      rcases packAux_first_mass L B [x] rest (L x) (by simp [groupLength]) hr with ⟨g, gs, he, hg⟩
      rw [he] at hi ⊢
      change B < groupLength L current.reverse + groupLength L g ∧ GroupsSeparated L B (g :: gs)
      refine ⟨?_, hi⟩
      rw [groupLength_reverse, hs]
      linarith

theorem greedyGroups_bounds {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α)
    (h : ∀ x ∈ items, 0 < L x ∧ L x ≤ B) :
    ∀ g ∈ greedyGroups L B items, g ≠ [] ∧ 0 < groupLength L g ∧ groupLength L g ≤ B := by
  cases items with
  | nil => simp [greedyGroups]
  | cons x rest =>
    have hx := h x (by simp)
    apply packAux_bounds L B [x] rest (L x) (by simp [groupLength]) hx.2 (by simp)
    · intro y hy
      have he : y = x := by simpa using hy
      subst y
      exact hx.1
    · intro y hy
      exact h y (by simp [hy])

theorem greedyGroups_separated {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α)
    (h : ∀ x ∈ items, 0 ≤ L x) : GroupsSeparated L B (greedyGroups L B items) := by
  cases items with
  | nil => trivial
  | cons x rest =>
    exact packAux_separated L B [x] rest (L x) (by simp [groupLength])
      (fun y hy => h y (by simp [hy]))

theorem groupLength_append {α : Type*} (L : α → ℝ) (a b : List α) :
    groupLength L (a ++ b) = groupLength L a + groupLength L b := by
  simp [groupLength, List.map_append, List.sum_append]

theorem groupLength_flatten {α : Type*} (L : α → ℝ) (groups : List (List α)) :
    groupLength L groups.flatten = (groups.map (groupLength L)).sum := by
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatten_cons, groupLength_append, ih]
    rfl

theorem separated_groups_count {α : Type*} (L : α → ℝ) (B : ℝ) (groups : List (List α))
    (hsep : GroupsSeparated L B groups) (hpos : ∀ g ∈ groups, 0 ≤ groupLength L g)
    (hmass : (groups.map (groupLength L)).sum ≤ 2 * B) : groups.length ≤ 3 := by
  cases groups with
  | nil => simp
  | cons g1 gs1 =>
    cases gs1 with
    | nil => simp
    | cons g2 gs2 =>
      cases gs2 with
      | nil => simp
      | cons g3 gs3 =>
        cases gs3 with
        | nil => simp
        | cons g4 rest =>
          have htail : 0 ≤ (rest.map (groupLength L)).sum := by
            apply List.sum_nonneg
            intro r hr
            rcases List.mem_map.mp hr with ⟨g, hg, rfl⟩
            exact hpos g (by simp [hg])
          have h12 := hsep.1
          have h34 := hsep.2.2.1
          simp only [List.map_cons, List.sum_cons] at hmass
          exfalso
          linarith

/-- The next-fit scan returns at most three groups whenever the total uniform
length is at most twice the budget. -/
theorem greedyGroups_count {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α)
    (h : ∀ x ∈ items, 0 < L x ∧ L x ≤ B) (hmass : groupLength L items ≤ 2 * B) :
    (greedyGroups L B items).length ≤ 3 := by
  have hgroups := greedyGroups_bounds L B items h
  have hsep := greedyGroups_separated L B items (fun x hx => le_of_lt (h x hx).1)
  apply separated_groups_count L B _ hsep (fun g hg => le_of_lt (hgroups g hg).2.1)
  rw [← groupLength_flatten, greedyGroups_flatten]
  exact hmass

end Blotto
