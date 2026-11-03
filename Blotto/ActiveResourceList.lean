import Blotto.ResourceRounding
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A maintained list of fractional coordinates. One update tests only the
selected pair; the untouched tail is reused. The vector is mathematical
functional-update semantics; an array representation and primitive-cost
refinement remain separate obligations. -/

namespace Blotto
open scoped BigOperators

noncomputable def retainedPair {n : ℕ} (L r : Allocation n) (a b : Fin n) : List (Fin n) := by
  classical
  exact [a, b].filter (fun j => decide (Fractional L r j))

theorem mem_retainedPair {n : ℕ} (L r : Allocation n) (a b j : Fin n) :
    j ∈ retainedPair L r a b ↔ (j = a ∨ j = b) ∧ Fractional L r j := by
  classical
  simp [retainedPair]

theorem retainedPair_sublist {n : ℕ} (L r : Allocation n) (a b : Fin n) :
    (retainedPair L r a b).Sublist [a, b] := List.filter_sublist

structure ActiveResourceList {n : ℕ} (L : Allocation n) where
  resource : Allocation n
  active : List (Fin n)
  nodup : active.Nodup
  membership : ∀ j, j ∈ active ↔ Fractional L resource j

namespace ActiveResourceList

theorem eq_of_fields {n : ℕ} {L : Allocation n} (s t : ActiveResourceList L)
    (hr : s.resource = t.resource) (ha : s.active = t.active) : s = t := by
  cases s
  cases t
  cases hr
  cases ha
  rfl

noncomputable def initial {n : ℕ} (L r : Allocation n) : ActiveResourceList L := by
  classical
  exact {
    resource := r
    active := (List.finRange n).filter (fun j => decide (Fractional L r j))
    nodup := (List.nodup_finRange n).filter _
    membership := by intro j; simp [List.mem_finRange] }

theorem length_eq_card {n : ℕ} {L : Allocation n} (s : ActiveResourceList L) :
    s.active.length = (fractionalSet L s.resource).card := by
  classical
  have he : s.active.toFinset = fractionalSet L s.resource := by
    ext j
    simp [s.membership j, mem_fractionalSet]
  rw [← List.toFinset_card_of_nodup s.nodup, he]

theorem initial_length_le {n : ℕ} (L r : Allocation n) : (initial L r).active.length ≤ n := by
  rw [length_eq_card]
  exact (Finset.card_le_univ _).trans (by simp)

theorem selected_distinct {n : ℕ} {L : Allocation n} (s : ActiveResourceList L)
    {a b : Fin n} {tail : List (Fin n)} (he : s.active = a :: b :: tail) : a ≠ b := by
  have hn := s.nodup
  rw [he, List.nodup_cons] at hn
  exact fun h => hn.1 (by simp [h])

theorem selected_fractional {n : ℕ} {L : Allocation n} (s : ActiveResourceList L)
    {a b : Fin n} {tail : List (Fin n)} (he : s.active = a :: b :: tail) :
    Fractional L s.resource a ∧ Fractional L s.resource b := by
  exact ⟨(s.membership a).mp (by simp [he]), (s.membership b).mp (by simp [he])⟩

noncomputable def update {n : ℕ} {L : Allocation n} (s : ActiveResourceList L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) : ActiveResourceList L where
  resource := updatePair s.resource a b z
  active := retainedPair L (updatePair s.resource a b z) a b ++ tail
  nodup := by
    have hn := s.nodup
    rw [he] at hn
    exact ((retainedPair_sublist L _ a b).append (List.Sublist.refl tail)).nodup hn
  membership := by
    intro j
    by_cases hja : j = a
    · subst j
      have hn := s.nodup
      rw [he, List.nodup_cons] at hn
      have hna : a ∉ tail := fun h => hn.1 (by simp [h])
      simp [mem_retainedPair, hna]
    · by_cases hjb : j = b
      · subst j
        have hn := s.nodup
        rw [he, List.nodup_cons, List.nodup_cons] at hn
        simp [mem_retainedPair, hn.2.1]
      · have hm : j ∈ tail ↔ Fractional L s.resource j := by simpa [he, hja, hjb] using s.membership j
        simp only [List.mem_append, mem_retainedPair, hja, hjb, false_or, false_and, hm]
        simp only [Fractional, updatePair_other s.resource hja hjb]

theorem update_length_lt {n : ℕ} {L : Allocation n} (s : ActiveResourceList L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail)
    {z : ℝ} (hz : z = (resourcePair L s.resource a b (s.selected_fractional he).1 (s.selected_fractional he).2).lower ∨
      z = (resourcePair L s.resource a b (s.selected_fractional he).1 (s.selected_fractional he).2).upper) :
    (s.update a b tail he z).active.length < s.active.length := by
  rw [length_eq_card, length_eq_card]
  exact updatePair_fractional_decreases (s.selected_distinct he)
    (s.selected_fractional he).1 (s.selected_fractional he).2 hz

theorem retainedPair_length_le_one {n : ℕ} {L : Allocation n} (s : ActiveResourceList L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail)
    {z : ℝ} (hz : z = (resourcePair L s.resource a b (s.selected_fractional he).1 (s.selected_fractional he).2).lower ∨
      z = (resourcePair L s.resource a b (s.selected_fractional he).1 (s.selected_fractional he).2).upper) :
    (retainedPair L (updatePair s.resource a b z) a b).length ≤ 1 := by
  have hl := s.update_length_lt a b tail he hz
  change (retainedPair L (updatePair s.resource a b z) a b ++ tail).length < s.active.length at hl
  rw [he, List.length_append] at hl
  simp only [List.length_cons] at hl
  omega

end ActiveResourceList
end Blotto
