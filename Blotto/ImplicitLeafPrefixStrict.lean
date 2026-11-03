import Blotto.ImplicitLeafInverse

/-! Exact positive labelled increments and cumulative crossings of stored
blocks. Prefix specifications sum labels only in proofs; executable queries
still scan stored blocks. Signed -1 denotes the empty prefix. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

theorem prefixMass_increment (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (code : Fin (C + 1)) :
    prefixMass blocks (code.val : ℤ) = prefixMass blocks ((code.val : ℤ) - 1) + labelMass blocks code.val := by
  rw [partition_prefixMass_labels C blocks hp, partition_prefixMass_labels C blocks hp]
  have he : ∀ label : Fin (C + 1),
      (if (label.val : ℤ) ≤ (code.val : ℤ) then labelMass blocks label.val else 0) =
        (if (label.val : ℤ) ≤ (code.val : ℤ) - 1 then labelMass blocks label.val else 0) +
          if label = code then labelMass blocks code.val else 0 := by
    intro label
    by_cases hEq : label = code
    · subst label
      simp
    · have hn : label.val ≠ code.val := fun h => hEq (Fin.ext h)
      by_cases hBefore : (label.val : ℤ) ≤ (code.val : ℤ) - 1
      · simp only [hBefore, show (label.val : ℤ) ≤ (code.val : ℤ) by omega, hEq, ite_true, ite_false, add_zero]
      · simp only [hBefore, show ¬(label.val : ℤ) ≤ (code.val : ℤ) by omega, hEq, ite_false, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hOne : (∑ label : Fin (C + 1), if label = code then labelMass blocks code.val else 0) =
      labelMass blocks code.val := by
    rw [Finset.sum_ite_eq']
    simp
  rw [hOne]

theorem prefixMass_increment_positive (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hw : Positive blocks) (code : Fin (C + 1)) :
    prefixMass blocks ((code.val : ℤ) - 1) < prefixMass blocks (code.val : ℤ) := by
  rw [prefixMass_increment C blocks hp code]
  exact lt_add_of_pos_right _ (partition_labelMass_positive C blocks hp hw code)

theorem prefixMass_strict_in_range (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hw : Positive blocks) {first last : ℤ} (hFirst : -1 ≤ first) (hLast : last ≤ (C : ℤ))
    (hOrder : first < last) : prefixMass blocks first < prefixMass blocks last := by
  have hNext : 0 ≤ first + 1 := by omega
  let code : Fin (C + 1) := ⟨(first + 1).toNat, by omega⟩
  have he : (code.val : ℤ) = first + 1 := by dsimp only [code]; omega
  have hi := prefixMass_increment_positive C blocks hp hw code
  rw [he] at hi
  have hm := prefixMass_mono blocks (fun b hb => (hw b hb).le) (show first + 1 ≤ last by omega)
  have hs : first + 1 - 1 = first := by omega
  rw [hs] at hi
  exact hi.trans_le hm

theorem inverseStrict_unique (C : ℕ) (blocks : List Block) (_hp : Partition C blocks) (hw : Positive blocks)
    (level : ℚ) (first last : Fin (C + 1))
    (hFirst : prefixMass blocks ((first.val : ℤ) - 1) ≤ level ∧ level < prefixMass blocks (first.val : ℤ))
    (hLast : prefixMass blocks ((last.val : ℤ) - 1) ≤ level ∧ level < prefixMass blocks (last.val : ℤ)) : first = last := by
  have hn : Nonnegative blocks := fun b hb => (hw b hb).le
  apply Fin.ext
  by_contra hNe
  rcases lt_or_gt_of_ne hNe with hLt | hGt
  · have hm := prefixMass_mono blocks hn (show (first.val : ℤ) ≤ (last.val : ℤ) - 1 by omega)
    linarith [hFirst.2, hLast.1]
  · have hm := prefixMass_mono blocks hn (show (last.val : ℤ) ≤ (first.val : ℤ) - 1 by omega)
    linarith [hLast.2, hFirst.1]

theorem inverseStrict_after (C : ℕ) (blocks : List Block) (_hp : Partition C blocks) (hw : Positive blocks)
    (level : ℚ) (cross : Fin (C + 1)) (cutoff : ℤ)
    (hCross : level < prefixMass blocks (cross.val : ℤ))
    (hLevel : prefixMass blocks cutoff ≤ level) : cutoff < (cross.val : ℤ) := by
  by_contra hn
  have hm := prefixMass_mono blocks (fun b hb => (hw b hb).le) (show (cross.val : ℤ) ≤ cutoff by omega)
  linarith

end Blotto.ImplicitLeafCounts
