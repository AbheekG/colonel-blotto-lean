import Blotto.GeneralPaperRayOracleSearch

/-! One rational crossing batch is filtered to the current closed bracket,
merge sorted, deduplicated by one traversal and stored once in an indexed
array. Both bracket endpoints are inserted. All eligible crossings remain,
with strict ordering and no new interior points.
-/
namespace Blotto.GeneralPaperRaySortedCrossings
set_option autoImplicit false
set_option maxHeartbeats 3500000

def after (last : ℚ) : List ℚ → List ℚ
  | [] => []
  | x::rest => if x=last then after last rest else x::after x rest

def unique : List ℚ → List ℚ
  | [] => []
  | x::rest => x::after x rest

theorem after_sublist (values : List ℚ) (last : ℚ) : (after last values).Sublist values := by
  induction values generalizing last with
  | nil => exact List.Sublist.refl _
  | cons x rest ih =>
    rw [after]
    split
    · exact List.Sublist.cons _ (ih last)
    · exact List.Sublist.cons_cons _ (ih x)

theorem unique_sublist (values : List ℚ) : (unique values).Sublist values := by
  cases values with
  | nil => exact List.Sublist.refl _
  | cons x rest => exact List.Sublist.cons_cons _ (after_sublist rest x)

theorem mem_after (x last : ℚ) (values : List ℚ) : x∈last::after last values ↔ x∈last::values := by
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

theorem mem_unique (x : ℚ) (values : List ℚ) : x∈unique values ↔ x∈values := by
  cases values with
  | nil => rfl
  | cons a rest => exact mem_after x a rest

theorem after_strict (values : List ℚ) (last : ℚ) (hSort : values.Pairwise (·≤·))
    (hLast : ∀ x∈values,last≤x) :
    (∀ x∈after last values,last<x) ∧ (after last values).Pairwise (·<·) := by
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
      have hx : last<x := by
        rcases lt_or_eq_of_le (hLast x (List.mem_cons_self)) with h|h
        · exact h
        · exact (hNe h.symm).elim
      have ht := ih x hs.2 hs.1
      refine ⟨?_,List.pairwise_cons.mpr ⟨ht.1,ht.2⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with hEq|hy
      · subst y; exact hx
      · exact hx.trans (ht.1 y hy)

theorem unique_strict (values : List ℚ) (hSort : values.Pairwise (·≤·)) : (unique values).Pairwise (·<·) := by
  cases values with
  | nil => exact List.Pairwise.nil
  | cons x rest =>
    have hs := List.pairwise_cons.mp hSort
    have he := after_strict rest x hs.2 hs.1
    exact List.pairwise_cons.mpr ⟨he.1,he.2⟩

def ordered (lo hi : ℚ) (points : List ℚ) : List ℚ :=
  unique ((lo::hi::points.filter (fun t => decide (lo≤t ∧ t≤hi))).mergeSort (·≤·))

theorem ordered_strict (lo hi : ℚ) (points : List ℚ) : (ordered lo hi points).Pairwise (·<·) := by
  apply unique_strict
  exact List.pairwise_mergeSort' (fun a b : ℚ => a≤b) _

theorem ordered_mem (lo hi : ℚ) (points : List ℚ) (t : ℚ) :
    t∈ordered lo hi points ↔ t=lo ∨ t=hi ∨ t∈points ∧ lo≤t ∧ t≤hi := by
  rw [ordered,mem_unique,List.mem_mergeSort]
  simp only [List.mem_cons,List.mem_filter,decide_eq_true_eq]

theorem lower_mem (lo hi : ℚ) (points : List ℚ) : lo∈ordered lo hi points := by rw [ordered_mem]; exact Or.inl rfl

theorem upper_mem (lo hi : ℚ) (points : List ℚ) : hi∈ordered lo hi points := by rw [ordered_mem]; exact Or.inr (Or.inl rfl)

theorem ordered_bound (lo hi : ℚ) (hOrder : lo≤hi) (points : List ℚ) (t : ℚ) (ht : t∈ordered lo hi points) : lo≤t ∧ t≤hi := by
  rw [ordered_mem] at ht
  rcases ht with rfl|rfl|⟨_,hl,hh⟩
  · exact ⟨le_rfl,hOrder⟩
  · exact ⟨hOrder,le_rfl⟩
  · exact ⟨hl,hh⟩

theorem ordered_length (lo hi : ℚ) (points : List ℚ) : (ordered lo hi points).length≤points.length+2 := by
  have he := (unique_sublist ((lo::hi::points.filter (fun t => decide (lo≤t ∧ t≤hi))).mergeSort (·≤·))).length_le
  simp only [List.length_mergeSort,List.length_cons] at he
  change (ordered lo hi points).length≤(points.filter (fun t => decide (lo≤t ∧ t≤hi))).length+1+1 at he
  have hf := List.length_filter_le (fun t => decide (lo≤t ∧ t≤hi)) points
  omega

def array (lo hi : ℚ) (points : List ℚ) : FixedArrayTable (ordered lo hi points).length ℚ :=
  ⟨(ordered lo hi points).toArray,by simp only [List.size_toArray]⟩

theorem array_read (lo hi : ℚ) (points : List ℚ) (i : Fin (ordered lo hi points).length) :
    (array lo hi points).read i=(ordered lo hi points).get i := by
  simp only [array,FixedArrayTable.read,List.getElem_toArray,List.get_eq_getElem]

theorem read_mem (lo hi : ℚ) (points : List ℚ) (i : Fin (ordered lo hi points).length) :
    (array lo hi points).read i∈ordered lo hi points := by
  rw [array_read]
  exact List.get_mem _ _

theorem mem_read (lo hi : ℚ) (points : List ℚ) (t : ℚ) (ht : t∈ordered lo hi points) :
    ∃ i,(array lo hi points).read i=t := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ht
  exact ⟨i,by rw [array_read]; exact hi⟩

theorem read_strict (lo hi : ℚ) (points : List ℚ) : StrictMono (array lo hi points).read := by
  intro i j hij
  rw [array_read,array_read]
  exact List.pairwise_iff_get.mp (ordered_strict lo hi points) i j hij

end Blotto.GeneralPaperRaySortedCrossings
