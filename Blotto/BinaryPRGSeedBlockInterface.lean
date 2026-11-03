import Blotto.BinaryPRGSeedBlockWork

/-! The native prepared blocks match the original exact flat seed-table gate
and every supplied bit. This identity supplies complete rejection and layout
refinement without a caller premise on block independence or reader values. -/

namespace Blotto.BinaryPRGSeedBlocks
open RationalLottoResourceSystem

theorem read_wrong_length (n K : ℕ) (seed : List Bool) (h : seed.length ≠ sampleBitBudget n K) : (read n K seed).1 = none := by
  cases hr : (read n K seed).1 with
  | none => rfl
  | some tables => exact False.elim (h (read_success_length n K seed tables hr))

theorem read_flat_state (n K : ℕ) (seed : List Bool) : (read n K seed).1.map Tables.flat =
    (RationalPRGBinaryRequest.seedTable (sampleBitBudget n K) seed).map FixedArrayTable.read := by
  by_cases h : seed.length = sampleBitBudget n K
  · let table : FixedArrayTable (sampleBitBudget n K) Bool := ⟨seed.toArray,by simpa using h⟩
    have hSeed : List.ofFn table.read = seed := by rw [listOfFn_read]
    rw [← hSeed,read_ofFn,RationalPRGBinaryRequest.seedTable_ofFn]
    simp only [Option.map_some,split_flat,arrayRead_ofFn]
  · rw [read_wrong_length n K seed h,RationalPRGBinaryRequest.seedTable_wrong_length _ seed h]
    rfl

theorem read_some_iff (n K : ℕ) (seed : List Bool) : (read n K seed).1.isSome = true ↔ seed.length = sampleBitBudget n K := by
  have hs := read_flat_state n K seed
  by_cases h : seed.length = sampleBitBudget n K
  · constructor
    · intro _; exact h
    · intro _
      unfold RationalPRGBinaryRequest.seedTable at hs
      rw [dite_eq_left h,Option.map_some] at hs
      cases hr : (read n K seed).1 with
      | none => rw [hr,Option.map_none] at hs; cases hs
      | some tables => rfl
  · rw [read_wrong_length n K seed h]
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
    exact h

end Blotto.BinaryPRGSeedBlocks
