import Blotto.PackingPartition
import Blotto.ResourceUpdate

/-! Uniform-coordinate grouping at a terminal resource vector. The only
possible fractional coordinate is kept out of every uniform group. -/

namespace Blotto
open scoped BigOperators

structure TerminalLotto (n : ℕ) where
  B : ℝ
  length : Allocation n
  resource : Allocation n
  B_pos : 0 < B
  length_pos : ∀ i, 0 < length i
  length_le : ∀ i, length i ≤ B
  box : InBox length resource
  resource_sum : (∑ i, resource i) = 2 * B
  fractional_le : (fractionalSet length resource).card ≤ 1

namespace TerminalLotto

noncomputable def uniformItems {n : ℕ} (i : TerminalLotto n) : List (Fin n) := by
  classical
  exact (List.finRange n).filter (fun j => decide (i.resource j = i.length j))

noncomputable def uniformSet {n : ℕ} (i : TerminalLotto n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => i.resource j = i.length j)

noncomputable def uniformMass {n : ℕ} (i : TerminalLotto n) : ℝ := groupLength i.length i.uniformItems

noncomputable def groups {n : ℕ} (i : TerminalLotto n) : List (List (Fin n)) := greedyGroups i.length i.B i.uniformItems

theorem mem_uniformItems {n : ℕ} (i : TerminalLotto n) (j : Fin n) : j ∈ i.uniformItems ↔ i.resource j = i.length j := by
  classical
  simp [uniformItems, List.mem_finRange]

theorem uniformItems_nodup {n : ℕ} (i : TerminalLotto n) : i.uniformItems.Nodup :=
  (List.nodup_finRange n).filter _

theorem uniformItems_toFinset {n : ℕ} (i : TerminalLotto n) : i.uniformItems.toFinset = i.uniformSet := by
  classical
  ext j
  simp [uniformSet, i.mem_uniformItems j]

theorem uniformMass_sum {n : ℕ} (i : TerminalLotto n) : i.uniformMass = ∑ j ∈ i.uniformSet, i.length j := by
  rw [← i.uniformItems_toFinset]
  exact (List.sum_toFinset i.length i.uniformItems_nodup).symm

theorem uniformMass_le {n : ℕ} (i : TerminalLotto n) : i.uniformMass ≤ 2 * i.B := by
  classical
  rw [i.uniformMass_sum]
  have he : (∑ j ∈ i.uniformSet, i.length j) = ∑ j ∈ i.uniformSet, i.resource j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ((Finset.mem_filter.mp hj).2).symm
  rw [he, ← i.resource_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => (i.box j).1)

theorem fractional_unique {n : ℕ} (i : TerminalLotto n) {a b : Fin n}
    (ha : Fractional i.length i.resource a) (hb : Fractional i.length i.resource b) : a = b := by
  by_contra hn
  have hc := Finset.one_lt_card.mpr ⟨a, (mem_fractionalSet _ _ _).mpr ha,
    b, (mem_fractionalSet _ _ _).mpr hb, hn⟩
  have hl := i.fractional_le
  omega

theorem endpoint_resource {n : ℕ} (i : TerminalLotto n) (j : Fin n)
    (hj : ¬Fractional i.length i.resource j) : i.resource j = 0 ∨ i.resource j = i.length j := by
  by_cases h0 : i.resource j = 0
  · exact Or.inl h0
  · have hp : 0 < i.resource j := lt_of_le_of_ne (i.box j).1 (Ne.symm h0)
    have hn : ¬i.resource j < i.length j := fun h => hj ⟨hp, h⟩
    exact Or.inr (le_antisymm (i.box j).2 (le_of_not_gt hn))

theorem uniformMass_no_fraction {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) : i.uniformMass = 2 * i.B := by
  classical
  have he : i.resource = fun j => if j ∈ i.uniformSet then i.length j else 0 := by
    funext j
    by_cases hj : j ∈ i.uniformSet
    · exact (by rw [ite_eq_left hj]; exact (Finset.mem_filter.mp hj).2)
    · have hr := i.endpoint_resource j (h j)
      rcases hr with h0 | hL
      · simp [hj, h0]
      · exact (hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩)).elim
  have hs := i.resource_sum
  rw [he, Finset.sum_ite_mem, Finset.univ_inter] at hs
  rw [i.uniformMass_sum]
  exact hs

theorem uniformMass_with_fraction {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : i.uniformMass + i.resource pivot = 2 * i.B := by
  classical
  have hpu : pivot ∉ i.uniformSet := by
    intro h
    have he := (Finset.mem_filter.mp h).2
    exact ne_of_lt hp.2 he
  have he : i.resource = fun j =>
      (if j ∈ i.uniformSet then i.length j else 0) + if j = pivot then i.resource pivot else 0 := by
    funext j
    by_cases hjp : j = pivot
    · subst j
      simp [hpu]
    · have hf : ¬Fractional i.length i.resource j := fun h => hjp (i.fractional_unique h hp)
      have hr := i.endpoint_resource j hf
      by_cases hj : j ∈ i.uniformSet
      · simp only [hj, hjp, ite_true, ite_false, add_zero]
        exact (Finset.mem_filter.mp hj).2
      · rcases hr with h0 | hL
        · simp [hj, hjp, h0]
        · exact (hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩)).elim
  have hs := i.resource_sum
  rw [he, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
  rw [i.uniformMass_sum]
  exact hs

theorem uniformMass_gt {n : ℕ} (i : TerminalLotto n) : i.B < i.uniformMass := by
  classical
  by_cases he : (fractionalSet i.length i.resource).Nonempty
  · rcases he with ⟨pivot, hp⟩
    have hf := (mem_fractionalSet _ _ _).mp hp
    have hs := i.uniformMass_with_fraction pivot hf
    have hb : i.resource pivot < i.B := lt_of_lt_of_le hf.2 (i.length_le pivot)
    linarith
  · have hf : ∀ j, ¬Fractional i.length i.resource j := by
      intro j hj
      exact he ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩
    rw [i.uniformMass_no_fraction hf]
    linarith [i.B_pos]

theorem groups_bounds {n : ℕ} (i : TerminalLotto n) :
    ∀ g ∈ i.groups, g ≠ [] ∧ 0 < groupLength i.length g ∧ groupLength i.length g ≤ i.B :=
  greedyGroups_bounds _ _ _ (fun j _ => ⟨i.length_pos j, i.length_le j⟩)

theorem groups_count_upper {n : ℕ} (i : TerminalLotto n) : i.groups.length ≤ 3 :=
  greedyGroups_count _ _ _ (fun j _ => ⟨i.length_pos j, i.length_le j⟩) i.uniformMass_le

theorem groups_mass {n : ℕ} (i : TerminalLotto n) : (i.groups.map (groupLength i.length)).sum = i.uniformMass := by
  rw [← groupLength_flatten, groups, greedyGroups_flatten]
  rfl

theorem groups_count_lower {n : ℕ} (i : TerminalLotto n) : 2 ≤ i.groups.length := by
  have hs := i.groups_mass
  have hb := i.groups_bounds
  have hgt := i.uniformMass_gt
  cases hg : i.groups with
  | nil => simp [hg] at hs; linarith [i.B_pos]
  | cons g rest =>
    cases rest with
    | nil =>
      have hB := (hb g (by simp [hg])).2.2
      simp [hg] at hs
      linarith
    | cons h tail => simp

end TerminalLotto
end Blotto
