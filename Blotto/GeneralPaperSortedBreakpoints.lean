import Blotto.GeneralPaperBoundaryCells
import Mathlib.Data.List.Sort

/-! Sort the finite breakpoint list, then remove adjacent repetitions in
one traversal. Both code endpoints are inserted and external points are
clipped to the alphabet endpoint. No full-code enumeration is performed.
Primitive sorting/bit and storage prices remain a separate source ledger.
-/
namespace Blotto.GeneralPaperSortedBreakpoints
set_option autoImplicit false
set_option maxHeartbeats 3500000

def after (last : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::rest => if x=last then after last rest else x::after x rest

def unique : List ℕ → List ℕ
  | [] => []
  | x::rest => x::after x rest

theorem after_sublist (values : List ℕ) (last : ℕ) : List.Sublist (after last values) values := by
  induction values generalizing last with
  | nil => exact List.Sublist.refl _
  | cons x rest ih =>
    rw [after]
    split
    · exact List.Sublist.cons _ (ih last)
    · exact List.Sublist.cons₂ _ (ih x)

theorem unique_sublist (values : List ℕ) : List.Sublist (unique values) values := by
  cases values with
  | nil => exact List.Sublist.refl _
  | cons x rest => exact List.Sublist.cons₂ _ (after_sublist rest x)

theorem mem_after (x last : ℕ) (values : List ℕ) : x∈last::after last values ↔ x∈last::values := by
  induction values generalizing last with
  | nil => rfl
  | cons a rest ih =>
    rw [after]
    split
    · rename_i hEq
      subst a
      have he := ih last
      simp only [List.mem_cons] at he ⊢
      tauto
    · have he := ih a
      simp only [List.mem_cons] at he ⊢
      tauto

theorem mem_unique (x : ℕ) (values : List ℕ) : x∈unique values ↔ x∈values := by
  cases values with
  | nil => rfl
  | cons a rest => exact mem_after x a rest

theorem after_strict (values : List ℕ) (last : ℕ) (hSort : values.Pairwise (·≤·))
    (hLast : ∀ x∈values, last≤x) :
    (∀ x∈after last values, last<x) ∧ (after last values).Pairwise (·<·) := by
  induction values generalizing last with
  | nil => simp [after]
  | cons x rest ih =>
    have hs := List.pairwise_cons.mp hSort
    rw [after]
    split
    · rename_i hEq
      subst x
      exact ih last hs.2 hs.1
    · rename_i hNe
      have hx : last<x := by have := hLast x (List.mem_cons_self); omega
      have ht := ih x hs.2 hs.1
      refine ⟨?_,List.pairwise_cons.mpr ⟨ht.1,ht.2⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with hEq|hy
      · subst y; exact hx
      · exact hx.trans (ht.1 y hy)

theorem unique_strict (values : List ℕ) (hSort : values.Pairwise (·≤·)) : (unique values).Pairwise (·<·) := by
  cases values with
  | nil => exact List.Pairwise.nil
  | cons x rest =>
    have hs := List.pairwise_cons.mp hSort
    have he := after_strict rest x hs.2 hs.1
    exact List.pairwise_cons.mpr ⟨he.1,he.2⟩

def ordered (U : ℕ) (points : List ℕ) : List ℕ := unique ((0::U::points.map (fun x => min x U)).mergeSort (·≤·))

theorem ordered_strict (U : ℕ) (points : List ℕ) : (ordered U points).Pairwise (·<·) := by
  apply unique_strict
  exact List.pairwise_mergeSort' (fun a b : ℕ => a≤b) _

theorem ordered_mem (U : ℕ) (points : List ℕ) (x : ℕ) :
    x∈ordered U points ↔ x∈0::U::points.map (fun x => min x U) := by
  rw [ordered,mem_unique,List.mem_mergeSort]

theorem zero_mem (U : ℕ) (points : List ℕ) : 0∈ordered U points := by rw [ordered_mem]; simp

theorem upper_mem (U : ℕ) (points : List ℕ) : U∈ordered U points := by rw [ordered_mem]; simp

theorem point_mem (U : ℕ) (points : List ℕ) (x : ℕ) (hX : x∈points) (hBound : x≤U) : x∈ordered U points := by
  rw [ordered_mem]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x,hX,Nat.min_eq_left hBound⟩))

theorem ordered_bound (U : ℕ) (points : List ℕ) (x : ℕ) (hX : x∈ordered U points) : x≤U := by
  rw [ordered_mem] at hX
  simp only [List.mem_cons,List.mem_map] at hX
  rcases hX with hX|hX|⟨y,_,rfl⟩
  · omega
  · omega
  · exact Nat.min_le_right _ _

theorem ordered_length (U : ℕ) (points : List ℕ) : (ordered U points).length≤points.length+2 := by
  have he := (unique_sublist ((0::U::points.map (fun x => min x U)).mergeSort (·≤·))).length_le
  simpa only [ordered,List.length_mergeSort,List.length_cons,List.length_map] using he

theorem ordered_positive (U : ℕ) (points : List ℕ) : 0<(ordered U points).length :=
  List.length_pos_of_mem (zero_mem U points)

end Blotto.GeneralPaperSortedBreakpoints
