import Blotto.ImplicitLeafPrefixStrict

/-! Exact masses of labelled code intervals. Prefix subtraction is used only
for the expanded exact-rational representation, not compact rounded prefixes. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

def intervalMass (blocks : List Block) (lo hi : ℕ) : ℚ :=
  prefixMass blocks (hi : ℤ) - prefixMass blocks ((lo : ℤ) - 1)

theorem intervalMass_labels (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (lo hi : ℕ) (hOrder : lo ≤ hi) :
    intervalMass blocks lo hi = ∑ code : Fin (C + 1),
      if lo ≤ code.val ∧ code.val ≤ hi then labelMass blocks code.val else 0 := by
  rw [intervalMass, partition_prefixMass_labels C blocks hp, partition_prefixMass_labels C blocks hp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro code _
  by_cases hLo : lo ≤ code.val
  · by_cases hHi : code.val ≤ hi
    · simp only [show (code.val : ℤ) ≤ (hi : ℤ) by omega,
        show ¬(code.val : ℤ) ≤ (lo : ℤ) - 1 by omega, hLo, hHi, and_self, ite_true, ite_false, sub_zero]
    · simp only [show ¬(code.val : ℤ) ≤ (hi : ℤ) by omega,
        show ¬(code.val : ℤ) ≤ (lo : ℤ) - 1 by omega, hLo, hHi, and_false, ite_false, sub_self]
  · have hHi : code.val ≤ hi := by omega
    simp only [show (code.val : ℤ) ≤ (hi : ℤ) by omega,
      show (code.val : ℤ) ≤ (lo : ℤ) - 1 by omega, hLo, hHi, false_and, ite_true, ite_false, sub_self]

theorem intervalMass_positive (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (lo hi : ℕ) (hOrder : lo ≤ hi) (hHi : hi ≤ C) : 0 < intervalMass blocks lo hi := by
  unfold intervalMass
  exact sub_pos.mpr (prefixMass_strict_in_range C blocks hp hw (by omega) (by omega) (by omega))

theorem intervalMass_append (blocks : List Block) (lo middle hi : ℕ) :
    intervalMass blocks lo middle + intervalMass blocks (middle + 1) hi = intervalMass blocks lo hi := by
  have he : ((middle + 1 : ℕ) : ℤ) - 1 = (middle : ℤ) := by omega
  unfold intervalMass
  rw [he]
  ring

theorem intervalMass_single (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (code : Fin (C + 1)) :
    intervalMass blocks code.val code.val = labelMass blocks code.val := by
  rw [intervalMass, prefixMass_increment C blocks hp code]
  ring

theorem intervalMass_full (C : ℕ) (blocks : List Block) (hp : Partition C blocks) :
    intervalMass blocks 0 C = totalMass blocks := by
  rw [intervalMass, partition_prefixMass_full C blocks hp (C : ℤ) le_rfl]
  norm_num only [Nat.cast_zero, zero_sub]
  rw [prefixMass_negative blocks (-1) (by norm_num)]
  simp

theorem intervalMass_prefix (blocks : List Block) (hi : ℕ) :
    intervalMass blocks 0 hi = prefixMass blocks (hi : ℤ) := by
  rw [intervalMass]
  norm_num only [Nat.cast_zero, zero_sub]
  rw [prefixMass_negative blocks (-1) (by norm_num)]
  simp

end Blotto.ImplicitLeafCounts
