import Blotto.CumulativeGuideSorting
import Blotto.CumulativeGuideSize

/-! Sorting and complete resource grouping preserve exact total mass. For
nonnegative resources with positive zero prefix, the actual lower-guide scan
retains that entire prefix as its first height. No first-height mass oracle or
Farey decoding assertion is used. -/

namespace Blotto
open scoped Classical
namespace CumulativeResourceGrouping
open CumulativeGuidePruning

theorem collect_totalMass (atoms : List Atom) (current : Atom) :
    totalMass (collect atoms current) = current.2 + totalMass atoms := by
  induction atoms generalizing current with
  | nil => simp [collect, totalMass]
  | cons atom rest ih =>
    dsimp only [collect]
    split_ifs
    · rw [ih]
      simp only [totalMass, List.map_cons, List.sum_cons]
      ring
    · simp only [totalMass, List.map_cons, List.sum_cons]
      change current.2 + totalMass (collect rest atom) = current.2 + (atom.2 + totalMass rest)
      rw [ih]

theorem group_totalMass (atoms : List Atom) : totalMass (group atoms) = totalMass atoms := by
  cases atoms with
  | nil => rfl
  | cons atom rest => exact collect_totalMass rest atom

theorem group_resources_nonnegative (atoms : List Atom) (h : ∀ atom ∈ atoms, 0 ≤ atom.1) :
    ∀ atom ∈ group atoms, 0 ≤ atom.1 := by
  cases atoms with
  | nil => simp [group]
  | cons current rest =>
    intro atom ha
    rcases collect_resource_origin rest current atom ha with he | ⟨source, hs, he⟩
    · rw [he]
      exact h current (by simp)
    · rw [he]
      exact h source (by simp [hs])

end CumulativeResourceGrouping

namespace CumulativeGuideSorting
open CumulativeGuidePruning CumulativeResourceGrouping

theorem sort_totalMass (atoms : List Atom) : totalMass (sort atoms) = totalMass atoms :=
  ((sort_perm atoms).map Prod.snd).sum_eq

theorem sorted_grouped_totalMass (atoms : List Atom) :
    totalMass (group (sort atoms)) = totalMass atoms := by rw [group_totalMass, sort_totalMass]

theorem sort_resources_nonnegative (atoms : List Atom) (h : ∀ atom ∈ atoms, 0 ≤ atom.1) :
    ∀ atom ∈ sort atoms, 0 ≤ atom.1 := fun atom ha => h atom ((sort_perm atoms).mem_iff.mp ha)

end CumulativeGuideSorting

namespace CumulativeGuidePruning
open CumulativeResourceGrouping CumulativeGuideSorting

theorem strictly_grouped_zero_prefix (atom : Atom) (rest : List Atom)
    (hSorted : StrictlyGrouped (atom :: rest)) (hResource : 0 ≤ atom.1) :
    prefixMass (atom :: rest) 0 = if atom.1 = 0 then atom.2 else 0 := by
  have hTail : ∀ next ∈ rest, (0 : ℝ) < (next.1 : ℝ) := by
    intro next hn
    have he := (List.pairwise_cons.mp hSorted).1 next hn
    have hp : 0 < next.1 := hResource.trans_lt he
    exact_mod_cast hp
  rw [prefixMass, prefixMass_zero_of_after rest 0 hTail, add_zero]
  have he : (atom.1 : ℝ) ≤ 0 ↔ atom.1 = 0 := by
    constructor
    · intro h
      have hq : atom.1 ≤ 0 := by exact_mod_cast h
      exact le_antisymm hq hResource
    · intro h
      simp [h]
  simp only [he]

theorem prune_first_height_zero_prefix (atoms : List Atom) (gamma : ℚ)
    (hSorted : StrictlyGrouped atoms) (hResources : ∀ atom ∈ atoms, 0 ≤ atom.1)
    (hZero : 0 < prefixMass atoms 0) :
    ∃ rest : List ℚ, cumulativeHeights (prune gamma atoms) 0 = prefixMass atoms 0 :: rest := by
  cases atoms with
  | nil => simp [prefixMass] at hZero
  | cons atom rest =>
    have he := strictly_grouped_zero_prefix atom rest hSorted (hResources atom (by simp))
    have hResource : atom.1 = 0 := by
      by_contra hn
      rw [ite_eq_right hn] at he
      rw [he] at hZero
      exact (lt_irrefl 0 hZero)
    rw [ite_eq_left hResource] at he
    have hMass : 0 < atom.2 := he ▸ hZero
    refine ⟨cumulativeHeights (scan gamma rest atom.2 atom.2) atom.2, ?_⟩
    rw [prune_first_positive rest gamma hMass]
    simp only [cumulativeHeights, zero_add, he]

theorem guideAtoms_first_height_zero_prefix (atoms : List Atom) (gamma : ℚ)
    (hResources : ∀ atom ∈ atoms, 0 ≤ atom.1) (hZero : 0 < prefixMass atoms 0) :
    ∃ rest : List ℚ, cumulativeHeights (guideAtoms atoms gamma) 0 = prefixMass atoms 0 :: rest := by
  have hSorted := group_strictly_grouped (sort atoms) (sort_nondecreasing atoms)
  have hResource := group_resources_nonnegative (sort atoms) (sort_resources_nonnegative atoms hResources)
  have hPrefix : prefixMass (group (sort atoms)) 0 = prefixMass atoms 0 := by
    rw [group_prefixMass, sort_prefixMass]
  have he := prune_first_height_zero_prefix (group (sort atoms)) gamma hSorted hResource (by rw [hPrefix]; exact hZero)
  simpa only [guideAtoms, hPrefix] using he

end CumulativeGuidePruning
end Blotto
