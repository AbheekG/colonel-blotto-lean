import Blotto.ImplicitLeafRange
import Blotto.GroupedGuideFirstHeight

/-! Polynomial-relevant logarithmic sizes for the actual conservative lower
guide of an expanded implicit leaf. Arbitrary duplicate nonnegative resources
are retained as labels. The finite atom view is proof data: efficient implicit
guide construction, Farey decoding and rounded block updates remain separate. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical
open CumulativeGuidePruning CumulativeResourceGrouping CumulativeGuideSorting

def leafAtoms (C : ℕ) (blocks : List Block) (resource : Fin (C + 1) → ℚ) : List Atom :=
  List.ofFn (fun code => (resource code, labelMass blocks code.val))

theorem leafAtoms_nonnegative (C : ℕ) (blocks : List Block) (resource : Fin (C + 1) → ℚ)
    (hw : ImplicitLeafCounts.Nonnegative blocks) : CumulativeGuidePruning.Nonnegative (leafAtoms C blocks resource) := by
  intro atom ha
  rcases List.mem_ofFn.mp ha with ⟨code, rfl⟩
  exact labelMass_nonnegative blocks code.val hw

theorem leafAtoms_resources_nonnegative (C : ℕ) (blocks : List Block) (resource : Fin (C + 1) → ℚ)
    (hr : ∀ code, 0 ≤ resource code) : ∀ atom ∈ leafAtoms C blocks resource, 0 ≤ atom.1 := by
  intro atom ha
  rcases List.mem_ofFn.mp ha with ⟨code, rfl⟩
  exact hr code

theorem leafAtoms_totalMass (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (resource : Fin (C + 1) → ℚ) :
    CumulativeGuidePruning.totalMass (leafAtoms C blocks resource) = ImplicitLeafCounts.totalMass blocks := by
  rw [partition_totalMass_labels C blocks hp]
  simp only [CumulativeGuidePruning.totalMass, leafAtoms, List.map_ofFn, List.sum_ofFn]
  rfl

theorem leafAtoms_zero_lower (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (resource : Fin (C + 1) → ℚ) (hw : ImplicitLeafCounts.Nonnegative blocks)
    (hzero : resource ⟨0, by omega⟩ = 0) :
    ImplicitLeafCounts.prefixMass blocks 0 ≤ CumulativeGuidePruning.prefixMass (leafAtoms C blocks resource) 0 := by
  rw [partition_prefix_zero C blocks hp, prefixMass_eq_list_sum]
  simp only [leafAtoms, List.map_ofFn, List.sum_ofFn]
  change labelMass blocks 0 ≤ ∑ code : Fin (C + 1),
    if (resource code : ℝ) ≤ 0 then labelMass blocks code.val else 0
  let zeroCode : Fin (C + 1) := ⟨0, by omega⟩
  have hZ : resource zeroCode = 0 := hzero
  have hb := Finset.single_le_sum (s := Finset.univ)
    (f := fun code : Fin (C + 1) => if (resource code : ℝ) ≤ 0 then labelMass blocks code.val else 0)
    (fun code _ => by
      split_ifs
      · exact labelMass_nonnegative blocks code.val hw
      · exact le_rfl)
    (Finset.mem_univ zeroCode)
  simpa only [hZ, Rat.cast_zero, le_refl, ite_true, zeroCode] using hb

theorem leafAtoms_zero_log_range (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (resource : Fin (C + 1) → ℚ) (hw : Positive blocks)
    (hzero : resource ⟨0, by omega⟩ = 0) :
    Real.log ((CumulativeGuidePruning.totalMass (leafAtoms C blocks resource) : ℝ) /
      (CumulativeGuidePruning.prefixMass (leafAtoms C blocks resource) 0 : ℝ)) ≤
        Real.log ((ImplicitLeafCounts.totalMass blocks : ℝ) / (ImplicitLeafCounts.prefixMass blocks 0 : ℝ)) := by
  have hNonneg : ImplicitLeafCounts.Nonnegative blocks := fun b hb => (hw b hb).le
  have hf : (0 : ℝ) < ImplicitLeafCounts.prefixMass blocks 0 := by
    exact_mod_cast partition_prefixMass_positive C blocks hp hw 0 le_rfl
  have hfirst : (ImplicitLeafCounts.prefixMass blocks 0 : ℝ) ≤
      CumulativeGuidePruning.prefixMass (leafAtoms C blocks resource) 0 := by
    exact_mod_cast leafAtoms_zero_lower C blocks hp resource hNonneg hzero
  have ht : (0 : ℝ) < ImplicitLeafCounts.totalMass blocks := by
    rw [← partition_prefixMass_full C blocks hp (C : ℤ) le_rfl]
    exact_mod_cast partition_prefixMass_positive C blocks hp hw (C : ℤ) (by omega)
  rw [leafAtoms_totalMass C blocks hp resource]
  exact Real.log_le_log (div_pos ht (hf.trans_le hfirst))
    (div_le_div_of_nonneg_left ht.le hf hfirst)

theorem guideAtoms_length_zero_log_bound (atoms : List Atom) (delta : ℚ)
    (hd : 0 < delta) (hu : delta ≤ 1) (hw : CumulativeGuidePruning.Nonnegative atoms)
    (hr : ∀ atom ∈ atoms, 0 ≤ atom.1) (hz : 0 < CumulativeGuidePruning.prefixMass atoms 0) :
    ((guideAtoms atoms (1 + delta)).length : ℝ) ≤ 1 +
      2 * Real.log ((CumulativeGuidePruning.totalMass atoms : ℝ) /
        (CumulativeGuidePruning.prefixMass atoms 0 : ℝ)) / (delta : ℝ) := by
  rcases guideAtoms_first_height_zero_prefix atoms (1 + delta) hr hz with ⟨rest, he⟩
  have hb := prune_length_log_bound (group (sort atoms)) delta hd hu
    (group_nonnegative _ (sort_nonnegative atoms hw)) (CumulativeGuidePruning.prefixMass atoms 0) rest he
  rw [sorted_grouped_totalMass] at hb
  exact hb

theorem leafGuide_length_range_bound (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (resource : Fin (C + 1) → ℚ) (hw : Positive blocks) (hr : ∀ code, 0 ≤ resource code)
    (hzero : resource ⟨0, by omega⟩ = 0) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1)
    (range : ℝ) (hRange : Real.log ((ImplicitLeafCounts.totalMass blocks : ℝ) /
      (ImplicitLeafCounts.prefixMass blocks 0 : ℝ)) ≤ range) :
    ((guideAtoms (leafAtoms C blocks resource) (1 + delta)).length : ℝ) ≤
      1 + 2 * range / (delta : ℝ) := by
  have hn : ImplicitLeafCounts.Nonnegative blocks := fun b hb => (hw b hb).le
  have hz : 0 < CumulativeGuidePruning.prefixMass (leafAtoms C blocks resource) 0 :=
    (partition_prefixMass_positive C blocks hp hw 0 le_rfl).trans_le
      (leafAtoms_zero_lower C blocks hp resource hn hzero)
  have hb := guideAtoms_length_zero_log_bound (leafAtoms C blocks resource) delta hd hu
    (leafAtoms_nonnegative C blocks resource hn) (leafAtoms_resources_nonnegative C blocks resource hr) hz
  have hl := (leafAtoms_zero_log_range C blocks hp resource hw hzero).trans hRange
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  exact hb.trans (add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 2)) hdR.le) 1)

theorem rounded_leafGuide_length_bound {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1)
    (past : List (Fin a)) (field : Fin m) (C : ℕ) (hs : sizes field = C + 1)
    (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (he : ∀ code : Fin (C + 1), labelMass blocks code.val =
      SparseMW.roundedFieldHistory selected localLoss eta theta past field (code.cast hs.symm))
    (resource : Fin (C + 1) → ℚ) (hr : ∀ code, 0 ≤ resource code)
    (hzero : resource ⟨0, by omega⟩ = 0) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((guideAtoms (leafAtoms C blocks resource) (1 + delta)).length : ℝ) ≤ 1 +
      2 * (Real.log ((C + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ) :=
  leafGuide_length_range_bound C blocks hp resource hw hr hzero delta hd hu _
    (rounded_history_log_range selected localLoss eta theta heta ht hl past field C hs blocks hp hw he)

end Blotto.ImplicitLeafCounts
