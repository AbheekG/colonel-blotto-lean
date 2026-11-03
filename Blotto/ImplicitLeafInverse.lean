import Blotto.ImplicitLeafCounts

/-! Exact strict cumulative inversion searches stored expanded rational blocks
linearly and solves the selected affine segment with rational floor. It does
not enumerate labels and makes no cached-search or Farey-resource claim. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

def affineInverse (block : Block) (level : ℚ) : ℕ := block.lo + ⌊level / block.weight⌋₊

def inverseWithVisits : List Block → ℚ → Option ℕ × ℕ
  | [], _ => (none, 0)
  | block :: rest, level =>
    let mass := ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight
    if level < mass then (some (affineInverse block level), 1)
    else
      let tail := inverseWithVisits rest (level - mass)
      (tail.1, tail.2 + 1)

def inverseStrict (blocks : List Block) (level : ℚ) : Option ℕ := (inverseWithVisits blocks level).1

theorem inverseWithVisits_bound (blocks : List Block) (level : ℚ) :
    (inverseWithVisits blocks level).2 ≤ blocks.length := by
  induction blocks generalizing level with
  | nil => exact le_rfl
  | cons block rest ih =>
    simp only [inverseWithVisits]
    split
    · simp
    · have he := ih (level - ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight)
      simpa only [List.length_cons] using Nat.add_le_add_right he 1

theorem affineInverse_contract (block : Block) (hOrder : block.lo ≤ block.hi)
    (hWeight : 0 < block.weight) (level : ℚ)
    (hLevel : 0 ≤ level ∧ level < ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight) :
    block.lo ≤ affineInverse block level ∧ affineInverse block level ≤ block.hi ∧
      blockMass block ((affineInverse block level : ℤ) - 1) ≤ level ∧
        level < blockMass block (affineInverse block level : ℤ) := by
  have hDiv : 0 ≤ level / block.weight := div_nonneg hLevel.1 hWeight.le
  have hFloor := Nat.floor_le hDiv
  have hNext := Nat.lt_floor_add_one (level / block.weight)
  have hRange : level / block.weight < ((block.hi + 1 - block.lo : ℕ) : ℚ) :=
    (div_lt_iff₀ hWeight).mpr hLevel.2
  have hNat : ⌊level / block.weight⌋₊ < block.hi + 1 - block.lo :=
    (Nat.floor_lt hDiv).mpr hRange
  have hk : affineInverse block level ≤ block.hi := by unfold affineInverse; omega
  have hLo : block.lo ≤ affineInverse block level := by unfold affineInverse; omega
  have hBefore : clippedCount block ((affineInverse block level : ℤ) - 1) = ⌊level / block.weight⌋₊ := by
    unfold clippedCount affineInverse
    omega
  have hThrough : clippedCount block (affineInverse block level : ℤ) = ⌊level / block.weight⌋₊ + 1 := by
    rw [clippedCount_nat]
    unfold affineInverse at hk ⊢
    omega
  refine ⟨hLo, hk, ?_, ?_⟩
  · unfold blockMass
    rw [hBefore]
    exact (le_div_iff₀ hWeight).mp hFloor
  · unfold blockMass
    rw [hThrough, Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ hWeight).mp hNext

theorem coversFrom_prefix_below (C next : ℕ) (blocks : List Block) (h : CoversFrom C next blocks)
    (cutoff : ℤ) (hCut : cutoff < next) : prefixMass blocks cutoff = 0 := by
  induction blocks generalizing next with
  | nil => rfl
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    have hc : clippedCount block cutoff = 0 := by unfold clippedCount; omega
    simp only [prefixMass, blockMass, hc, Nat.cast_zero, zero_mul, zero_add]
    exact ih (block.hi + 1) h.2.2 (by omega)

theorem inverseStrict_contract_from (C next : ℕ) (blocks : List Block)
    (hPartition : CoversFrom C next blocks) (hWeights : Positive blocks) (level : ℚ)
    (hLevel : 0 ≤ level ∧ level < totalMass blocks) :
    ∃ code, inverseStrict blocks level = some code ∧ next ≤ code ∧ code ≤ C ∧
      prefixMass blocks ((code : ℤ) - 1) ≤ level ∧ level < prefixMass blocks (code : ℤ) := by
  induction blocks generalizing next level with
  | nil => simp only [totalMass, List.map_nil, List.sum_nil] at hLevel; linarith
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at hPartition
    have hw := hWeights block (by simp)
    let mass : ℚ := ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight
    have hTotal : totalMass (block :: rest) = mass + totalMass rest := rfl
    by_cases hCross : level < mass
    · have hc := affineInverse_contract block hPartition.2.1 hw level ⟨hLevel.1, hCross⟩
      refine ⟨affineInverse block level, ?_, by omega, ?_, ?_, ?_⟩
      · dsimp only [mass] at hCross
        simp only [inverseStrict, inverseWithVisits, hCross, ite_true]
      · have hb := coversFrom_start_bound C (block.hi + 1) rest hPartition.2.2
        omega
      · rw [prefixMass, coversFrom_prefix_below C (block.hi + 1) rest hPartition.2.2 _ (by omega), add_zero]
        exact hc.2.2.1
      · rw [prefixMass, coversFrom_prefix_below C (block.hi + 1) rest hPartition.2.2 _ (by omega), add_zero]
        exact hc.2.2.2
    · have hSub : 0 ≤ level - mass ∧ level - mass < totalMass rest := by
        rw [hTotal] at hLevel
        constructor <;> linarith
      rcases ih (block.hi + 1) hPartition.2.2 (fun atom ha => hWeights atom (by simp [ha]))
        (level - mass) hSub with ⟨code, hInv, hLo, hHi, hBefore, hThrough⟩
      refine ⟨code, ?_, by omega, hHi, ?_, ?_⟩
      · change (inverseWithVisits (block :: rest) level).1 = some code
        dsimp only [mass] at hCross
        simp only [inverseWithVisits, hCross, ite_false]
        exact hInv
      · rw [prefixMass]
        have hb : blockMass block ((code : ℤ) - 1) = mass := by
          unfold blockMass mass
          rw [clippedCount_full block _ (by omega)]
        rw [hb]
        linarith
      · rw [prefixMass]
        have hb : blockMass block (code : ℤ) = mass := by
          unfold blockMass mass
          rw [clippedCount_full block _ (by omega)]
        rw [hb]
        linarith

theorem inverseStrict_contract (C : ℕ) (blocks : List Block) (hPartition : Partition C blocks)
    (hWeights : Positive blocks) (level : ℚ) (hLevel : 0 ≤ level ∧ level < totalMass blocks) :
    ∃ code : Fin (C + 1), inverseStrict blocks level = some code.val ∧
      prefixMass blocks ((code.val : ℤ) - 1) ≤ level ∧ level < prefixMass blocks (code.val : ℤ) := by
  rcases inverseStrict_contract_from C 0 blocks hPartition hWeights level hLevel with ⟨code, hi, _, hc, hb, ht⟩
  exact ⟨⟨code, by omega⟩, hi, hb, ht⟩

end ImplicitLeafCounts
end Blotto
