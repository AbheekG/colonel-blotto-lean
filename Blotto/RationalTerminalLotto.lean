import Blotto.RationalProportionalGroups
import Blotto.TerminalLottoLaw

/-! Native terminal Lotto grouping and computable fractional-coordinate
selection. The at-most-one-fractional invariant is an erased certificate. -/

namespace Blotto
open scoped BigOperators

structure RationalTerminalLotto (n : ℕ) where
  B : ℚ
  length : Fin n → ℚ
  resource : Fin n → ℚ
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  box : ∀ j, 0 ≤ resource j ∧ resource j ≤ length j
  resource_sum : (∑ j, resource j) = 2 * B
  fractional_le : (fractionalSet (fun j => (length j : ℝ)) (fun j => (resource j : ℝ))).card ≤ 1

namespace RationalTerminalLotto

noncomputable def real {n : ℕ} (i : RationalTerminalLotto n) : TerminalLotto n where
  B := i.B
  length := fun j => i.length j
  resource := fun j => i.resource j
  B_pos := by exact_mod_cast i.B_pos
  length_pos := fun j => by exact_mod_cast i.length_pos j
  length_le := fun j => by exact_mod_cast i.length_le j
  box := fun j => by
    change (0 : ℝ) ≤ (i.resource j : ℝ) ∧ (i.resource j : ℝ) ≤ (i.length j : ℝ)
    exact_mod_cast i.box j
  resource_sum := by exact_mod_cast i.resource_sum
  fractional_le := i.fractional_le

def uniformItems {n : ℕ} (i : RationalTerminalLotto n) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (i.resource j = i.length j))

def fractionalItems {n : ℕ} (i : RationalTerminalLotto n) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (0 < i.resource j ∧ i.resource j < i.length j))

def pivot {n : ℕ} (i : RationalTerminalLotto n) : Option (Fin n) := i.fractionalItems.head?

def uniformMass {n : ℕ} (i : RationalTerminalLotto n) : ℚ := rationalGroupLength i.length i.uniformItems

def groups {n : ℕ} (i : RationalTerminalLotto n) : List (List (Fin n)) :=
  rationalGreedyGroups i.length i.B i.uniformItems

theorem fractional_iff {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n) :
    Fractional i.real.length i.real.resource j ↔ 0 < i.resource j ∧ i.resource j < i.length j := by
  dsimp [Fractional, real]
  norm_cast

theorem uniformItems_real {n : ℕ} (i : RationalTerminalLotto n) : i.uniformItems = i.real.uniformItems := by
  classical
  unfold uniformItems TerminalLotto.uniformItems
  congr 1
  funext j
  simp [real, Rat.cast_inj]

theorem uniformMass_real {n : ℕ} (i : RationalTerminalLotto n) : (i.uniformMass : ℝ) = i.real.uniformMass := by
  rw [uniformMass, rationalGroupLength_real, i.uniformItems_real]
  rfl

theorem groups_real {n : ℕ} (i : RationalTerminalLotto n) : i.groups = i.real.groups := by
  rw [groups, rationalGreedyGroups_real, i.uniformItems_real]
  rfl

theorem mem_uniformItems {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n) :
    j ∈ i.uniformItems ↔ i.resource j = i.length j := by
  simp [uniformItems, List.mem_finRange]

theorem mem_fractionalItems {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n) :
    j ∈ i.fractionalItems ↔ 0 < i.resource j ∧ i.resource j < i.length j := by
  simp [fractionalItems, List.mem_finRange]

theorem uniformItems_nodup {n : ℕ} (i : RationalTerminalLotto n) : i.uniformItems.Nodup :=
  (List.nodup_finRange n).filter _

theorem groups_flatten {n : ℕ} (i : RationalTerminalLotto n) : i.groups.flatten = i.uniformItems :=
  rationalGreedyGroups_flatten _ _ _

theorem groups_nodup {n : ℕ} (i : RationalTerminalLotto n) : i.groups.flatten.Nodup := by
  rw [i.groups_flatten]
  exact i.uniformItems_nodup

theorem groups_bounds {n : ℕ} (i : RationalTerminalLotto n) :
    ∀ g ∈ i.groups, g ≠ [] ∧ 0 < rationalGroupLength i.length g ∧ rationalGroupLength i.length g ≤ i.B :=
  rationalGreedyGroups_bounds _ _ _ (fun j _ => ⟨i.length_pos j, i.length_le j⟩)

theorem groups_count {n : ℕ} (i : RationalTerminalLotto n) : i.groups.length = 2 ∨ i.groups.length = 3 := by
  rw [i.groups_real]
  exact i.real.groups_count

theorem uniformMass_le {n : ℕ} (i : RationalTerminalLotto n) : i.uniformMass ≤ 2 * i.B := by
  have h := i.real.uniformMass_le
  rw [← i.uniformMass_real] at h
  change (i.uniformMass : ℝ) ≤ 2 * (i.B : ℝ) at h
  exact_mod_cast h

theorem uniformMass_gt {n : ℕ} (i : RationalTerminalLotto n) : i.B < i.uniformMass := by
  have h := i.real.uniformMass_gt
  rw [← i.uniformMass_real] at h
  change (i.B : ℝ) < (i.uniformMass : ℝ) at h
  exact_mod_cast h

theorem fractional_unique {n : ℕ} (i : RationalTerminalLotto n) {a b : Fin n}
    (ha : 0 < i.resource a ∧ i.resource a < i.length a)
    (hb : 0 < i.resource b ∧ i.resource b < i.length b) : a = b :=
  i.real.fractional_unique ((i.fractional_iff a).mpr ha) ((i.fractional_iff b).mpr hb)

theorem pivot_none {n : ℕ} (i : RationalTerminalLotto n) (h : i.pivot = none) :
    ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j) := by
  have he : i.fractionalItems = [] := List.head?_eq_none_iff.mp h
  intro j hj
  have hm := (i.mem_fractionalItems j).mpr hj
  simp [he] at hm

theorem pivot_some {n : ℕ} (i : RationalTerminalLotto n) {j : Fin n} (h : i.pivot = some j) :
    0 < i.resource j ∧ i.resource j < i.length j := by
  exact (i.mem_fractionalItems j).mp (List.mem_of_head? h)

theorem uniformMass_no_fraction {n : ℕ} (i : RationalTerminalLotto n)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) : i.uniformMass = 2 * i.B := by
  have he := i.real.uniformMass_no_fraction (fun j hj => h j ((i.fractional_iff j).mp hj))
  rw [← i.uniformMass_real] at he
  change (i.uniformMass : ℝ) = 2 * (i.B : ℝ) at he
  exact_mod_cast he

theorem uniformMass_with_fraction {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n)
    (hj : 0 < i.resource j ∧ i.resource j < i.length j) : i.uniformMass + i.resource j = 2 * i.B := by
  have he := i.real.uniformMass_with_fraction j ((i.fractional_iff j).mpr hj)
  rw [← i.uniformMass_real] at he
  change (i.uniformMass : ℝ) + (i.resource j : ℝ) = 2 * (i.B : ℝ) at he
  exact_mod_cast he

def partition {n : ℕ} (i : RationalTerminalLotto n) : RationalProportionalGroups n i.groups.length where
  length := i.length
  length_pos := i.length_pos
  members := fun g => i.groups.get g
  nodup := fun g => (List.nodup_flatten.mp i.groups_nodup).1 _ (List.get_mem _ g)
  disjoint := by
    intro g h hgh
    have hp := List.pairwise_iff_get.mp (List.nodup_flatten.mp i.groups_nodup).2
    rcases lt_or_gt_of_ne hgh with hlt | hlt
    · exact hp g h hlt
    · exact (hp h g hlt).symm
  totalData := RationalResourceArray.ofAllocation (fun g => rationalGroupLength i.length (i.groups.get g))
  total_eq := by intro g; simp [RationalResourceArray.allocation_ofAllocation]
  total_pos := by
    intro g
    rw [RationalResourceArray.allocation_ofAllocation]
    exact (i.groups_bounds _ (List.get_mem _ g)).2.1

theorem partition_covers {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n) :
    (∃ g, j ∈ i.partition.members g) ↔ i.resource j = i.length j := by
  rw [← i.mem_uniformItems j, ← i.groups_flatten]
  constructor
  · rintro ⟨g, hg⟩
    exact List.mem_flatten.mpr ⟨_, List.get_mem _ g, hg⟩
  · intro hj
    rcases List.mem_flatten.mp hj with ⟨xs, hx, hjx⟩
    rcases List.mem_iff_get.mp hx with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change j ∈ i.groups.get g
    rw [hg]
    exact hjx

theorem partition_total_le {n : ℕ} (i : RationalTerminalLotto n) (g : Fin i.groups.length) :
    i.partition.total g ≤ i.B := by
  change (RationalResourceArray.ofAllocation _).allocation g ≤ i.B
  rw [RationalResourceArray.allocation_ofAllocation]
  exact (i.groups_bounds _ (List.get_mem _ g)).2.2

theorem partition_mass {n : ℕ} (i : RationalTerminalLotto n) : (∑ g, i.partition.total g) = i.uniformMass := by
  simp only [RationalProportionalGroups.total, partition, RationalResourceArray.allocation_ofAllocation]
  have he : ((∑ g : Fin i.groups.length, rationalGroupLength i.length (i.groups.get g)) : ℚ) =
      (i.groups.map (rationalGroupLength i.length)).sum := by simp
  rw [he]
  have hr : ((i.groups.map (rationalGroupLength i.length)).sum : ℝ) = (i.uniformMass : ℝ) := by
    push_cast
    simp only [List.map_map, Function.comp_def, rationalGroupLength_real]
    rw [← groupLength_flatten, i.groups_flatten]
    exact (rationalGroupLength_real _ _).symm
  exact_mod_cast hr

end RationalTerminalLotto
end Blotto
