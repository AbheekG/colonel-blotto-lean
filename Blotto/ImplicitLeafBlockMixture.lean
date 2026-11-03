import Blotto.ImplicitLeafCounts

/-! Selecting an exact clipped block by mass and then a uniform original label
has the original prefix-weighted law. Label sums are semantic proof data only;
the two-stage runtime works over stored blocks and bounded integer sampling. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

def blockLabels (C : ℕ) (block : Block) (cutoff : ℤ) : Finset (Fin (C + 1)) :=
  Finset.univ.filter (fun code => contains block code.val ∧ (code.val : ℤ) ≤ cutoff)

noncomputable def blockMean (C : ℕ) (block : Block) (cutoff : ℤ) (test : Fin (C + 1) → ℝ) : ℝ :=
  (∑ code ∈ blockLabels C block cutoff, test code) / (clippedCount block cutoff : ℝ)

noncomputable def blockMixtureMean (C : ℕ) (blocks : List Block) (cutoff : ℤ) (test : Fin (C + 1) → ℝ) : ℝ :=
  ((blocks.map (fun block => (blockMass block cutoff : ℝ) * blockMean C block cutoff test)).sum) /
    (prefixMass blocks cutoff : ℝ)

theorem blockLabels_card (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C) :
    (blockLabels C block cutoff).card = clippedCount block cutoff := clippedCount_card C block cutoff hHi

theorem zero_count_label_sum (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (hz : clippedCount block cutoff = 0) (test : Fin (C + 1) → ℝ) :
    (∑ code ∈ blockLabels C block cutoff, test code) = 0 := by
  have hc := blockLabels_card C block cutoff hHi
  rw [hz] at hc
  have he := Finset.card_eq_zero.mp hc
  rw [he, Finset.sum_empty]

theorem blockMass_mul_mean (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (test : Fin (C + 1) → ℝ) :
    (blockMass block cutoff : ℝ) * blockMean C block cutoff test =
      (block.weight : ℝ) * ∑ code ∈ blockLabels C block cutoff, test code := by
  by_cases hz : clippedCount block cutoff = 0
  · rw [zero_count_label_sum C block cutoff hHi hz test]
    simp [blockMass, hz]
  · have hc : (clippedCount block cutoff : ℝ) ≠ 0 := by exact_mod_cast hz
    unfold blockMass blockMean
    push_cast
    field_simp

theorem block_weighted_sum (C : ℕ) (block : Block) (cutoff : ℤ) (test : Fin (C + 1) → ℝ) :
    (block.weight : ℝ) * (∑ code ∈ blockLabels C block cutoff, test code) =
      ∑ code : Fin (C + 1), if contains block code.val ∧ (code.val : ℤ) ≤ cutoff
        then (block.weight : ℝ) * test code else 0 := by
  rw [Finset.mul_sum]
  unfold blockLabels
  rw [Finset.sum_filter]

theorem blocks_weighted_sum (C : ℕ) (blocks : List Block) (cutoff : ℤ)
    (hBounds : ∀ block ∈ blocks, block.hi ≤ C) (test : Fin (C + 1) → ℝ) :
    (blocks.map (fun block => (blockMass block cutoff : ℝ) * blockMean C block cutoff test)).sum =
      ∑ code : Fin (C + 1), if (code.val : ℤ) ≤ cutoff then (labelMass blocks code.val : ℝ) * test code else 0 := by
  induction blocks with
  | nil => simp [labelMass]
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [blockMass_mul_mean C block cutoff (hBounds block (by simp)), block_weighted_sum,
      ih (fun b hb => hBounds b (by simp [hb])), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro code _
    simp only [labelMass, Rat.cast_add]
    by_cases hCut : (code.val : ℤ) ≤ cutoff
    · cases contains block code.val
      · simp only [hCut, Bool.false_eq_true, false_and, ite_false, ite_true, Rat.cast_zero, zero_add]
      · simp only [hCut, true_and, ite_true]
        ring
    · simp only [hCut, and_false, ite_false, add_zero]

theorem blockMixtureMean_exact (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (cutoff : ℤ) (test : Fin (C + 1) → ℝ) :
    blockMixtureMean C blocks cutoff test =
      (∑ code : Fin (C + 1), if (code.val : ℤ) ≤ cutoff then (labelMass blocks code.val : ℝ) * test code else 0) /
        (prefixMass blocks cutoff : ℝ) := by
  unfold blockMixtureMean
  rw [blocks_weighted_sum C blocks cutoff (fun block hb => (coversFrom_bounds C 0 blocks hp block hb).2.2)]

theorem blockMean_bounds (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (test : Fin (C + 1) → ℝ) (ht : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    0 ≤ blockMean C block cutoff test ∧ blockMean C block cutoff test ≤ 1 := by
  have hs : 0 ≤ ∑ code ∈ blockLabels C block cutoff, test code := Finset.sum_nonneg (fun code _ => (ht code).1)
  have hu : (∑ code ∈ blockLabels C block cutoff, test code) ≤ (clippedCount block cutoff : ℝ) := by
    calc
      _ ≤ ∑ _code ∈ blockLabels C block cutoff, (1 : ℝ) := Finset.sum_le_sum (fun code _ => (ht code).2)
      _ = _ := by simp [blockLabels_card C block cutoff hHi]
  unfold blockMean
  by_cases hz : clippedCount block cutoff = 0
  · simp [hz]
  · have hc : (0 : ℝ) < clippedCount block cutoff := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact ⟨div_nonneg hs hc.le, (div_le_one hc).mpr hu⟩

def offsetLabel (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (offset : Fin (clippedCount block cutoff)) : Fin (C + 1) :=
  ⟨block.lo + offset.val, by
    have hc := offset.isLt
    unfold clippedCount at hc
    omega⟩

theorem offsetLabel_mem (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (offset : Fin (clippedCount block cutoff)) : offsetLabel C block cutoff hHi offset ∈ blockLabels C block cutoff := by
  simp only [blockLabels, Finset.mem_filter, Finset.mem_univ, true_and, contains, decide_eq_true_eq, offsetLabel]
  have hc := offset.isLt
  unfold clippedCount at hc
  omega

def offsetEquiv (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C) :
    Fin (clippedCount block cutoff) ≃ {label : Fin (C + 1) // label ∈ blockLabels C block cutoff} where
  toFun := fun offset => ⟨offsetLabel C block cutoff hHi offset, offsetLabel_mem C block cutoff hHi offset⟩
  invFun := fun label => ⟨label.val.val - block.lo, by
    have hm := label.property
    simp only [blockLabels, Finset.mem_filter, Finset.mem_univ, true_and, contains, decide_eq_true_eq] at hm
    unfold clippedCount
    omega⟩
  left_inv := by
    intro offset
    apply Fin.ext
    simp only [offsetLabel]
    omega
  right_inv := by
    intro label
    apply Subtype.ext
    apply Fin.ext
    have hm := label.property
    simp only [blockLabels, Finset.mem_filter, Finset.mem_univ, true_and, contains, decide_eq_true_eq] at hm
    simp only [offsetLabel]
    omega

theorem uniform_offsets_mean (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C)
    (test : Fin (C + 1) → ℝ) :
    (∑ offset : Fin (clippedCount block cutoff), test (offsetLabel C block cutoff hHi offset)) /
      (clippedCount block cutoff : ℝ) = blockMean C block cutoff test := by
  unfold blockMean
  congr 1
  calc
    (∑ offset : Fin (clippedCount block cutoff), test (offsetLabel C block cutoff hHi offset)) =
        ∑ label : {label : Fin (C + 1) // label ∈ blockLabels C block cutoff}, test label.val := by
      exact Equiv.sum_comp (offsetEquiv C block cutoff hHi) (fun label => test label.val)
    _ = _ := Finset.sum_coe_sort (blockLabels C block cutoff) test

end Blotto.ImplicitLeafCounts
