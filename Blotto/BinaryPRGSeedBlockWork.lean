import Blotto.BinaryPRGSeedBlockRefinement

/-! Every seed-preparation rejection/success path has a bound independent of
supplied seed length. Ruler/cursor visits and conservative array cell-copy
allowances derive from the declared schedule. This does not certify scalar,
array ownership/address/backend or physical machine/space costs. -/

namespace Blotto.BinaryPRGSeedBlocks
open RationalLottoResourceSystem

theorem read_rulers (n K : ℕ) (seed : List Bool) : (read n K seed).2.rulers = coinBitBudget n K + K := by
  unfold read
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

def cursorBound (count : ℕ) : ℕ := 5 * (count + 3) + 1

theorem read_cursors_bound (n K : ℕ) (seed : List Bool) : (read n K seed).2.cursors ≤ cursorBound (sampleBitBudget n K) := by
  have hC := BinarySeedCursor.consume_bound (List.replicate (coinBitBudget n K) false) seed
  simp only [List.length_replicate] at hC
  unfold read
  dsimp only
  split
  · change (BinarySeedCursor.consume (List.replicate (coinBitBudget n K) false) seed).2 ≤ _
    unfold cursorBound sampleBitBudget innerBitBudget
    omega
  · rename_i first hc
    have hS := BinarySeedCursor.consume_bound (List.replicate K false) first.2
    simp only [List.length_replicate] at hS
    split
    · change (BinarySeedCursor.consume (List.replicate (coinBitBudget n K) false) seed).2 +
        (BinarySeedCursor.consume (List.replicate K false) first.2).2 ≤ _
      unfold cursorBound sampleBitBudget innerBitBudget
      omega
    · rename_i second hs
      have hO := BinarySeedCursor.consume_bound (List.replicate K false) second.2
      simp only [List.length_replicate] at hO
      split
      · change (BinarySeedCursor.consume (List.replicate (coinBitBudget n K) false) seed).2 +
          (BinarySeedCursor.consume (List.replicate K false) first.2).2 + (BinarySeedCursor.consume (List.replicate K false) second.2).2 ≤ _
        unfold cursorBound sampleBitBudget innerBitBudget
        omega
      · split <;> change (BinarySeedCursor.consume (List.replicate (coinBitBudget n K) false) seed).2 +
          (BinarySeedCursor.consume (List.replicate K false) first.2).2 + (BinarySeedCursor.consume (List.replicate K false) second.2).2 + 1 ≤ _ <;>
          unfold cursorBound sampleBitBudget innerBitBudget <;> omega

theorem arrayCellAllowance_add (a b : ℕ) : arrayCellAllowance a + arrayCellAllowance b ≤ arrayCellAllowance (a + b) := by
  unfold arrayCellAllowance
  nlinarith

theorem read_arrays_bound (n K : ℕ) (seed : List Bool) : (read n K seed).2.arrays ≤ arrayCellAllowance (sampleBitBudget n K) := by
  unfold read
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i first hc
    have hC := (BinarySeedCursor.consume_success (List.replicate (coinBitBudget n K) false) seed first.1 first.2 hc).1
    simp only [List.length_replicate] at hC
    split
    · exact Nat.zero_le _
    · rename_i second hs
      have hS := (BinarySeedCursor.consume_success (List.replicate K false) first.2 second.1 second.2 hs).1
      simp only [List.length_replicate] at hS
      split
      · exact Nat.zero_le _
      · rename_i third ho
        have hO := (BinarySeedCursor.consume_success (List.replicate K false) second.2 third.1 third.2 ho).1
        simp only [List.length_replicate] at hO
        split
        · change arrayCellAllowance first.1.length + arrayCellAllowance second.1.length + arrayCellAllowance third.1.length ≤ _
          rw [hC,hS,hO]
          exact (Nat.add_le_add_right (arrayCellAllowance_add (coinBitBudget n K) K) (arrayCellAllowance K)).trans
            (arrayCellAllowance_add (coinBitBudget n K + K) K)
        · exact Nat.zero_le _

theorem read_arrays_of_reject (n K : ℕ) (seed : List Bool) (h : (read n K seed).1 = none) : (read n K seed).2.arrays = 0 := by
  revert h
  unfold read
  dsimp only
  split
  · intro h; rfl
  · split
    · intro h; rfl
    · split
      · intro h; rfl
      · split
        · intro h; cases h
        · intro h; rfl

def bound (count : ℕ) : ℕ := count + cursorBound count + arrayCellAllowance count

theorem read_bound (n K : ℕ) (seed : List Bool) : (read n K seed).2.recorded ≤ bound (sampleBitBudget n K) := by
  have hr := read_rulers n K seed
  have hc := read_cursors_bound n K seed
  have ha := read_arrays_bound n K seed
  have hR : (read n K seed).2.rulers ≤ sampleBitBudget n K := by
    rw [hr]
    unfold sampleBitBudget innerBitBudget
    omega
  unfold Ledger.recorded bound
  omega

theorem bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b := by
  unfold bound cursorBound arrayCellAllowance
  gcongr

theorem bound_square (count : ℕ) : bound count ≤ (count + 5) ^ 2 := by
  unfold bound cursorBound arrayCellAllowance
  nlinarith

end Blotto.BinaryPRGSeedBlocks
