import Blotto.BinaryPRGSeedBlocks

/-! Prepared seed blocks exactly realize the original nested flat-bit layout.
The split/flat maps here are correspondence specifications; the native driver
uses the three stored arrays directly. No independence or seed-layout premise
is supplied by a caller. -/

namespace Blotto.BinaryPRGSeedBlocks
open RationalLottoResourceSystem

theorem Tables.outer_eq {n K : ℕ} (tables : Tables n K) :
    secondBitBlock (innerBitBudget n K) K tables.flat = tables.outer.read := by
  funext j
  change (Fin.append (Fin.append tables.choice.read tables.scalar.read) tables.outer.read) (Fin.natAdd (innerBitBudget n K) j) = _
  exact Fin.append_right _ _ j

theorem Tables.inner_eq {n K : ℕ} (tables : Tables n K) :
    firstBitBlock (innerBitBudget n K) K tables.flat = Fin.append tables.choice.read tables.scalar.read := by
  funext j
  change (Fin.append (Fin.append tables.choice.read tables.scalar.read) tables.outer.read) (Fin.castAdd K j) = _
  exact Fin.append_left _ _ j

theorem Tables.scalar_eq {n K : ℕ} (tables : Tables n K) :
    secondBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K tables.flat) = tables.scalar.read := by
  rw [tables.inner_eq]
  funext j
  exact Fin.append_right _ _ j

theorem Tables.choice_eq {n K : ℕ} (tables : Tables n K) :
    firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K tables.flat) = tables.choice.read := by
  rw [tables.inner_eq]
  funext j
  exact Fin.append_left _ _ j

def split (n K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : Tables n K :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  { choice := FixedArrayTable.ofFn (firstBitBlock (coinBitBudget n K) K inner)
    scalar := FixedArrayTable.ofFn (secondBitBlock (coinBitBudget n K) K inner)
    outer := FixedArrayTable.ofFn (secondBitBlock (innerBitBudget n K) K bits) }

theorem arrayRead_ofFn {m : ℕ} (bits : Fin m → Bool) : (FixedArrayTable.ofFn bits).read = bits :=
  funext (FixedArrayTable.read_ofFn bits)

theorem split_flat (n K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : (split n K bits).flat = bits := by
  let inner := firstBitBlock (innerBitBudget n K) K bits
  have hInner : Fin.append (firstBitBlock (coinBitBudget n K) K inner) (secondBitBlock (coinBitBudget n K) K inner) = inner :=
    @Fin.append_castAdd_natAdd (coinBitBudget n K) K Bool inner
  have hOuter : Fin.append inner (secondBitBlock (innerBitBudget n K) K bits) = bits :=
    @Fin.append_castAdd_natAdd (innerBitBudget n K) K Bool bits
  unfold split Tables.flat
  simp only [arrayRead_ofFn]
  exact (congrArg (fun reader : Fin (innerBitBudget n K) → Bool =>
    Fin.append reader (secondBitBlock (innerBitBudget n K) K bits)) hInner).trans hOuter

theorem read_append (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (read n K (choice ++ (scalar ++ outer))).1 = some (pack n K choice scalar outer hc hs ho) := by
  have hC := BinarySeedCursor.consume_append (List.replicate (coinBitBudget n K) false) choice (scalar ++ outer) (by simpa only [List.length_replicate] using hc)
  have hS := BinarySeedCursor.consume_append (List.replicate K false) scalar outer (by simpa only [List.length_replicate] using hs)
  have hO := BinarySeedCursor.consume_append (List.replicate K false) outer [] (by simpa only [List.length_replicate] using ho)
  simp only [List.append_nil] at hO
  unfold read
  dsimp only
  split
  · rename_i hNone
    rw [hC] at hNone
    cases hNone
  · rename_i first hf
    have hPair : first = (choice,scalar ++ outer) := Option.some.inj (hf.symm.trans hC)
    cases hPair
    dsimp only
    split
    · rename_i hNone
      rw [hS] at hNone
      cases hNone
    · rename_i second hg
      have hPair : second = (scalar,outer) := Option.some.inj (hg.symm.trans hS)
      cases hPair
      dsimp only
      split
      · rename_i hNone
        rw [hO] at hNone
        cases hNone
      · rename_i third hh
        have hPair : third = (outer,[]) := Option.some.inj (hh.symm.trans hO)
        cases hPair
        rfl

theorem read_ofFn (n K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    (read n K (List.ofFn bits)).1 = some (split n K bits) := by
  let tables := split n K bits
  have hC : tables.choice.data.toList.length = coinBitBudget n K := by simp [tables.choice.size]
  have hS : tables.scalar.data.toList.length = K := by simp [tables.scalar.size]
  have hO : tables.outer.data.toList.length = K := by simp [tables.outer.size]
  have hInput : List.ofFn bits = tables.choice.data.toList ++ (tables.scalar.data.toList ++ tables.outer.data.toList) := by
    rw [← split_flat n K bits]
    rw [Tables.flat_ofFn]
    exact List.append_assoc _ _ _
  rw [hInput,read_append n K _ _ _ hC hS hO]
  congr 1
  apply Tables.ext <;> rfl

end Blotto.BinaryPRGSeedBlocks
