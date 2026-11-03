import Blotto.ImplicitLeafGuideSize
import Blotto.ImplicitLeafUpperGuideSize
import Blotto.CumulativeInternalGuide

/-! The actual internal pair/sort/group/prune guide has logarithmic retained
size. Pair enumeration is still charged construction work; retained support is
controlled by the child total/zero-prefix ratios, not the Cartesian pair count. -/

namespace Blotto
open scoped BigOperators Classical
namespace CumulativeInternalGuide
open CumulativeGuidePruning CumulativeGuideSorting

def familyTotal {n : ℕ} (family : RationalWeightedFamily n) : ℚ := ∑ label, family.mass label

theorem rationalFamily_total (atoms : List Atom) (hn : Nonnegative atoms) :
    familyTotal (rationalFamily atoms hn) = totalMass atoms := by
  unfold familyTotal rationalFamily totalMass
  change (∑ label : Fin atoms.length, atoms[label].2) = (atoms.map Prod.snd).sum
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map atoms Prod.snd)

theorem pairAtoms_total {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m) :
    totalMass (pairAtoms left right) = familyTotal left * familyTotal right := by
  unfold totalMass pairAtoms
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  change (∑ i, ∑ j, left.mass i * right.mass j) = _
  simp only [← Finset.mul_sum, ← Finset.sum_mul, familyTotal]

theorem pairAtoms_resources_nonnegative {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m)
    (hl : ∀ label, 0 ≤ left.resource label) (hr : ∀ label, 0 ≤ right.resource label) :
    ∀ atom ∈ pairAtoms left right, 0 ≤ atom.1 := by
  intro atom ha
  rcases List.mem_ofFn.mp ha with ⟨label, rfl⟩
  exact add_nonneg (hl _) (hr _)

theorem pairAtoms_zero {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m)
    (hl : ∀ label, 0 ≤ left.resource label) (hr : ∀ label, 0 ≤ right.resource label) :
    prefixMass (pairAtoms left right) 0 = left.prefixMass 0 * right.prefixMass 0 := by
  rw [prefixMass_eq_list_sum]
  unfold pairAtoms
  rw [List.map_ofFn, List.sum_ofFn, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  dsimp only
  unfold RationalWeightedFamily.prefixMass
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [Function.comp_def]
  rw [Equiv.symm_apply_apply]
  have hsum : ((left.resource i + right.resource j : ℚ) : ℝ) ≤ 0 ↔ left.resource i ≤ 0 ∧ right.resource j ≤ 0 := by
    constructor
    · intro h
      have hq : left.resource i + right.resource j ≤ 0 := by exact_mod_cast h
      constructor <;> linarith [hl i, hr j]
    · intro h
      exact_mod_cast add_nonpos h.1 h.2
  simp only [hsum]
  split_ifs <;> simp_all

theorem guideAtoms_zero_exact (atoms : List Atom) (gamma : ℚ) (_hg : 1 ≤ gamma)
    (hr : ∀ atom ∈ atoms, 0 ≤ atom.1) (hz : 0 < prefixMass atoms 0) :
    prefixMass (guideAtoms atoms gamma) 0 = prefixMass atoms 0 := by
  let groups := CumulativeResourceGrouping.group (sort atoms)
  have hs := CumulativeResourceGrouping.group_strictly_grouped (sort atoms) (sort_nondecreasing atoms)
  have hres := CumulativeResourceGrouping.group_resources_nonnegative (sort atoms) (sort_resources_nonnegative atoms hr)
  have hprefix : prefixMass groups 0 = prefixMass atoms 0 := by
    rw [CumulativeResourceGrouping.group_prefixMass, sort_prefixMass]
  cases hGroups : groups with
  | nil => simp only [hGroups, prefixMass] at hprefix; linarith
  | cons atom rest =>
    have hZero := strictly_grouped_zero_prefix atom rest (by rw [← hGroups]; exact hs)
      (hres atom (by change atom ∈ groups; rw [hGroups]; simp))
    have hAtomZero : atom.1 = 0 := by
      by_contra hn
      rw [ite_eq_right hn] at hZero
      have hp : 0 < prefixMass (atom :: rest) 0 := by rw [← hGroups, hprefix]; exact hz
      rw [hZero] at hp
      exact lt_irrefl _ hp
    rw [ite_eq_left hAtomZero] at hZero
    have hMass : 0 < atom.2 := by rw [← hZero, ← hGroups, hprefix]; exact hz
    have hTail : ∀ next ∈ rest, (0 : ℝ) < (next.1 : ℝ) := by
      intro next hn
      have hgt := (List.pairwise_cons.mp (show StrictlyGrouped (atom :: rest) from by rw [← hGroups]; exact hs)).1 next hn
      rw [hAtomZero] at hgt
      exact_mod_cast hgt
    change prefixMass (prune gamma groups) 0 = _
    rw [hGroups, prune_first_positive rest gamma hMass, prefixMass]
    rw [scan_prefixMass_zero_of_after rest gamma atom.2 atom.2 0 hTail]
    simp only [hAtomZero, Rat.cast_zero, le_refl, ite_true, add_zero]
    rw [← hZero, ← hGroups, hprefix]

theorem internalGuide_zero {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m)
    (hl : ∀ label, 0 ≤ left.resource label) (hr : ∀ label, 0 ≤ right.resource label)
    (hpl : 0 < left.prefixMass 0) (hpr : 0 < right.prefixMass 0) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (internalGuide left right gamma).prefixMass 0 = left.prefixMass 0 * right.prefixMass 0 := by
  have hZero := pairAtoms_zero left right hl hr
  have hp : 0 < prefixMass (pairAtoms left right) 0 := by rw [hZero]; exact mul_pos hpl hpr
  have he := guideAtoms_zero_exact (pairAtoms left right) gamma hg (pairAtoms_resources_nonnegative left right hl hr) hp
  have hFamily : (internalGuide left right gamma).prefixMass 0 = prefixMass (guideAtoms (pairAtoms left right) gamma) 0 := by
    unfold internalGuide guideFamily rationalFamily RationalWeightedFamily.prefixMass
    rw [prefixMass_eq_sum]
    apply Finset.sum_congr rfl
    intro label _
    have hc : ((guideAtoms (pairAtoms left right) gamma)[label].1 : ℝ) ≤ 0 ↔ (guideAtoms (pairAtoms left right) gamma)[label].1 ≤ 0 := by norm_cast
    simp only [hc]
  rw [hFamily, he, hZero]

theorem internalGuide_total_bound {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m)
    (gamma : ℚ) (hg : 1 ≤ gamma) :
    familyTotal (internalGuide left right gamma) ≤ familyTotal left * familyTotal right := by
  have he := scan_total_envelope (CumulativeResourceGrouping.group (sort (pairAtoms left right))) gamma 0 0 hg
    (CumulativeResourceGrouping.group_nonnegative _ (sort_nonnegative _ (pairAtoms_nonnegative left right)))
    le_rfl le_rfl le_rfl (by simp)
  simp only [zero_add] at he
  have hFirst := he.1
  change totalMass (guideAtoms (pairAtoms left right) gamma) ≤ _ at hFirst
  unfold internalGuide guideFamily
  rw [rationalFamily_total, ← pairAtoms_total left right]
  exact hFirst.trans_eq (sorted_grouped_totalMass _)

theorem internalGuide_length_log_bound {n m : ℕ} (left : RationalWeightedFamily n) (right : RationalWeightedFamily m)
    (hl : ∀ label, 0 ≤ left.resource label) (hr : ∀ label, 0 ≤ right.resource label)
    (hpl : 0 < left.prefixMass 0) (hpr : 0 < right.prefixMass 0)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((guideAtoms (pairAtoms left right) (1 + delta)).length : ℝ) ≤
      1 + 2 * Real.log (((familyTotal left * familyTotal right : ℚ) : ℝ) /
        ((left.prefixMass 0 * right.prefixMass 0 : ℚ) : ℝ)) / (delta : ℝ) := by
  have hp : 0 < prefixMass (pairAtoms left right) 0 := by
    rw [pairAtoms_zero left right hl hr]
    exact mul_pos hpl hpr
  have he := ImplicitLeafCounts.guideAtoms_length_zero_log_bound (pairAtoms left right) delta hd hu (pairAtoms_nonnegative left right)
    (pairAtoms_resources_nonnegative left right hl hr) hp
  rw [pairAtoms_total, pairAtoms_zero left right hl hr] at he
  exact he

end CumulativeInternalGuide
end Blotto
