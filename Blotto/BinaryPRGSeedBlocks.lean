import Blotto.BinarySeedCursor
import Blotto.BinaryScalarTape

/-! One native seed preparation consumes choice/scalar/outer blocks with
Boolean rulers and requires an empty final suffix. Rejected seeds build no
arrays. Successful arrays retain the exact original flat layout. Cell-copy
allowances permit full prefix copying; scalar/array/address/physical backend
and whole-machine/space claims remain separate. -/

namespace Blotto.BinaryPRGSeedBlocks
open RationalLottoResourceSystem

structure Tables (n K : ℕ) where
  choice : FixedArrayTable (coinBitBudget n K) Bool
  scalar : FixedArrayTable K Bool
  outer : FixedArrayTable K Bool
  scalarView : BinaryScalarTape K := BinaryScalarTape.ofFn scalar.read
  outerView : BinaryScalarTape K := BinaryScalarTape.ofFn outer.read
  scalarView_read : scalarView.read = scalar.read := by exact BinaryScalarTape.ofFn_read _
  outerView_read : outerView.read = outer.read := by exact BinaryScalarTape.ofFn_read _

attribute [simp] Tables.scalarView_read Tables.outerView_read

@[ext] theorem Tables.ext {n K : ℕ} {first second : Tables n K}
    (hc : first.choice = second.choice) (hs : first.scalar = second.scalar)
    (ho : first.outer = second.outer) : first = second := by
  cases first with
  | mk c s o sv ov hS hO =>
    cases second with
    | mk c' s' o' sv' ov' hS' hO' =>
      dsimp only at hc hs ho
      subst c'
      subst s'
      subst o'
      have hSV := BinaryScalarTape.ext (hS.trans hS'.symm)
      have hOV := BinaryScalarTape.ext (hO.trans hO'.symm)
      cases hSV
      cases hOV
      rfl

def Tables.flat {n K : ℕ} (tables : Tables n K) : Fin (sampleBitBudget n K) → Bool :=
  Fin.append (Fin.append tables.choice.read tables.scalar.read) tables.outer.read

def Tables.flatList {n K : ℕ} (tables : Tables n K) : List Bool :=
  tables.choice.data.toList ++ tables.scalar.data.toList ++ tables.outer.data.toList

theorem listOfFn_read {n : ℕ} (table : FixedArrayTable n Bool) : List.ofFn table.read = table.data.toList := by
  rcases table with ⟨data,hs⟩
  subst n
  change @List.ofFn Bool data.size (fun j : Fin data.size => data[j.val]) = data.toList
  simpa only [Array.length_toList,Array.getElem_toList] using (List.ofFn_getElem (xs := data.toList))

theorem Tables.flat_ofFn {n K : ℕ} (tables : Tables n K) : List.ofFn tables.flat = tables.flatList := by
  unfold Tables.flat Tables.flatList
  change @List.ofFn Bool (coinBitBudget n K + K + K) (Fin.append (Fin.append tables.choice.read tables.scalar.read) tables.outer.read) = _
  rw [List.ofFn_fin_append,List.ofFn_fin_append,listOfFn_read,listOfFn_read,listOfFn_read]

theorem Tables.flatList_length {n K : ℕ} (tables : Tables n K) : tables.flatList.length = sampleBitBudget n K := by
  rw [← tables.flat_ofFn,List.length_ofFn]

def pack (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) : Tables n K :=
  let c : FixedArrayTable (coinBitBudget n K) Bool := ⟨choice.toArray,by simpa using hc⟩
  let s : FixedArrayTable K Bool := ⟨scalar.toArray,by simpa using hs⟩
  let o : FixedArrayTable K Bool := ⟨outer.toArray,by simpa using ho⟩
  ⟨c,s,o,⟨scalar,hs⟩,⟨outer,ho⟩,
    BinaryScalarTape.read_eq_array _ _ (by simp [s]),
    BinaryScalarTape.read_eq_array _ _ (by simp [o])⟩

@[simp] theorem pack_scalar_tape (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (pack n K choice scalar outer hc hs ho).scalarView.bits = scalar := rfl

@[simp] theorem pack_outer_tape (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (pack n K choice scalar outer hc hs ho).outerView.bits = outer := rfl

theorem pack_flatList (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (pack n K choice scalar outer hc hs ho).flatList = choice ++ scalar ++ outer := by
  simp [pack,Tables.flatList]

structure Ledger where
  rulers : ℕ
  cursors : ℕ
  arrays : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.rulers + ledger.cursors + ledger.arrays

def arrayCellAllowance (length : ℕ) : ℕ := length * (length + 1) + 2 * length

def read (n K : ℕ) (seed : List Bool) : Option (Tables n K) × Ledger :=
  let choiceRuler := List.replicate (coinBitBudget n K) false
  let precisionRuler := List.replicate K false
  let rulers := coinBitBudget n K + K
  let choice := BinarySeedCursor.consume choiceRuler seed
  match hc : choice.1 with
  | none => (none,⟨rulers,choice.2,0⟩)
  | some first =>
      let scalar := BinarySeedCursor.consume precisionRuler first.2
      match hs : scalar.1 with
      | none => (none,⟨rulers,choice.2 + scalar.2,0⟩)
      | some second =>
          let outer := BinarySeedCursor.consume precisionRuler second.2
          match ho : outer.1 with
          | none => (none,⟨rulers,choice.2 + scalar.2 + outer.2,0⟩)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2 hc).1
                  simpa only [choiceRuler,List.length_replicate] using h
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2 hs).1
                  simpa only [precisionRuler,List.length_replicate] using h
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2 ho).1
                  simpa only [precisionRuler,List.length_replicate] using h
                (some (pack n K first.1 second.1 third.1 hChoice hScalar hOuter),
                  ⟨rulers,choice.2 + scalar.2 + outer.2 + 1,
                    arrayCellAllowance first.1.length + arrayCellAllowance second.1.length + arrayCellAllowance third.1.length⟩)
              else (none,⟨rulers,choice.2 + scalar.2 + outer.2 + 1,0⟩)

theorem read_success_flatList (n K : ℕ) (seed : List Bool) (tables : Tables n K)
    (h : (read n K seed).1 = some tables) : tables.flatList = seed := by
  unfold read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i first hc
    have hC := BinarySeedCursor.consume_success (List.replicate (coinBitBudget n K) false) seed first.1 first.2 hc
    split at h
    · cases h
    · rename_i second hs
      have hS := BinarySeedCursor.consume_success (List.replicate K false) first.2 second.1 second.2 hs
      split at h
      · cases h
      · rename_i third ho
        have hO := BinarySeedCursor.consume_success (List.replicate K false) second.2 third.1 third.2 ho
        split at h
        · rename_i hEnd
          cases Option.some.inj h
          rw [pack_flatList,hC.2,hS.2,hO.2,hEnd,List.append_nil,List.append_assoc]
        · cases h

theorem read_success_length (n K : ℕ) (seed : List Bool) (tables : Tables n K)
    (h : (read n K seed).1 = some tables) : seed.length = sampleBitBudget n K := by
  rw [← read_success_flatList n K seed tables h]
  exact tables.flatList_length

end Blotto.BinaryPRGSeedBlocks
