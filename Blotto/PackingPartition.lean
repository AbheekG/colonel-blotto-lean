import Blotto.GreedyPacking
import Blotto.ProportionalGroups

/-! The greedy scan's list partition as the disjoint group data used by
proportional allocation splitting. -/

namespace Blotto
open scoped BigOperators

theorem list_index_sum {α : Type*} (f : α → ℝ) (items : List α) :
    (∑ i : Fin items.length, f (items.get i)) = (items.map f).sum := by
  simp

noncomputable def packingPartition {n : ℕ} (L : Allocation n) (hL : ∀ i, 0 < L i)
    (B : ℝ) (items : List (Fin n)) (hitems : items.Nodup)
    (hbound : ∀ i ∈ items, L i ≤ B) : ProportionalGroups n (greedyGroups L B items).length where
  length := L
  length_pos := hL
  members := fun g => ((greedyGroups L B items).get g).toFinset
  disjoint := by
    intro g h hgh
    have hn : (greedyGroups L B items).flatten.Nodup := by rw [greedyGroups_flatten]; exact hitems
    have hp := (List.nodup_flatten.mp hn).2
    have hpair := List.pairwise_iff_get.mp hp
    apply Finset.disjoint_left.mpr
    intro i hi hg
    have hi' : i ∈ (greedyGroups L B items).get g := by simpa using hi
    have hg' : i ∈ (greedyGroups L B items).get h := by simpa using hg
    rcases lt_or_gt_of_ne hgh with hlt | hlt
    · exact (List.disjoint_left.mp (hpair g h hlt)) hi' hg'
    · exact (List.disjoint_left.mp (hpair h g hlt)) hg' hi'
  total_pos := by
    intro g
    have hn : (greedyGroups L B items).flatten.Nodup := by rw [greedyGroups_flatten]; exact hitems
    have hgn := (List.nodup_flatten.mp hn).1 _ (List.get_mem _ g)
    rw [List.sum_toFinset L hgn]
    have hg := greedyGroups_bounds L B items (fun i hi => ⟨hL i, hbound i hi⟩)
      ((greedyGroups L B items).get g) (List.get_mem _ g)
    exact hg.2.1

theorem packingPartition_total {n : ℕ} (L : Allocation n) (hL : ∀ i, 0 < L i)
    (B : ℝ) (items : List (Fin n)) (hitems : items.Nodup) (hbound : ∀ i ∈ items, L i ≤ B)
    (g : Fin (greedyGroups L B items).length) :
    (packingPartition L hL B items hitems hbound).total g =
      groupLength L ((greedyGroups L B items).get g) := by
  have hn : (greedyGroups L B items).flatten.Nodup := by rw [greedyGroups_flatten]; exact hitems
  have hgn := (List.nodup_flatten.mp hn).1 _ (List.get_mem _ g)
  exact List.sum_toFinset L hgn

theorem packingPartition_total_bound {n : ℕ} (L : Allocation n) (hL : ∀ i, 0 < L i)
    (B : ℝ) (items : List (Fin n)) (hitems : items.Nodup) (hbound : ∀ i ∈ items, L i ≤ B)
    (g : Fin (greedyGroups L B items).length) :
    (packingPartition L hL B items hitems hbound).total g ≤ B := by
  rw [packingPartition_total]
  exact (greedyGroups_bounds L B items (fun i hi => ⟨hL i, hbound i hi⟩)
    _ (List.get_mem _ g)).2.2

theorem packingPartition_covers {n : ℕ} (L : Allocation n) (hL : ∀ i, 0 < L i)
    (B : ℝ) (items : List (Fin n)) (hitems : items.Nodup) (hbound : ∀ i ∈ items, L i ≤ B)
    (i : Fin n) :
    (∃ g, i ∈ (packingPartition L hL B items hitems hbound).members g) ↔ i ∈ items := by
  constructor
  · rintro ⟨g, hg⟩
    have hm : i ∈ (greedyGroups L B items).get g := by simpa [packingPartition] using hg
    have hf : i ∈ (greedyGroups L B items).flatten := List.mem_flatten.mpr ⟨_, List.get_mem _ g, hm⟩
    rwa [greedyGroups_flatten] at hf
  · intro hi
    have hf : i ∈ (greedyGroups L B items).flatten := by rwa [greedyGroups_flatten]
    rcases List.mem_flatten.mp hf with ⟨g, hg, hgi⟩
    rcases List.mem_iff_get.mp hg with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change i ∈ ((greedyGroups L B items).get j).toFinset
    rw [List.mem_toFinset, hj]
    exact hgi

theorem packingPartition_mass {n : ℕ} (L : Allocation n) (hL : ∀ i, 0 < L i)
    (B : ℝ) (items : List (Fin n)) (hitems : items.Nodup) (hbound : ∀ i ∈ items, L i ≤ B) :
    (∑ g, (packingPartition L hL B items hitems hbound).total g) = groupLength L items := by
  simp only [packingPartition_total]
  rw [list_index_sum, ← groupLength_flatten, greedyGroups_flatten]

end Blotto
