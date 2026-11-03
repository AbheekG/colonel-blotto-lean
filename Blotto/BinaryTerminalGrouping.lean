import Blotto.BinaryGreedyPacking
import Blotto.BinaryResourceState
import Blotto.RationalTerminalLotto

/-! Native terminal uniform/fractional scans and original-order greedy grouping
use stored Boolean resource/length words. Source terminal validity is proof-only;
all group lists and cached totals are computed, not supplied as a factory. -/

namespace Blotto.BinaryTerminalGrouping
open BinaryRationalNormalization BinaryRationalEncoding

structure Input (n : ℕ) where
  budget : SignedWord
  length : FixedArrayTable n SignedWord
  resource : FixedArrayTable n SignedWord

def Input.Canonical {n : ℕ} (input : Input n) : Prop := CanonicalWord input.budget ∧
  (∀ j, CanonicalWord (input.length.read j)) ∧ (∀ j, CanonicalWord (input.resource.read j))

def Input.Refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n) : Prop :=
  value input.budget = source.B ∧ (∀ j, value (input.length.read j) = source.length j) ∧
    (∀ j, value (input.resource.read j) = source.resource j)

def uniform {n : ℕ} (input : Input n) (j : Fin n) : Bool :=
  BinaryRationalArithmetic.lessEqual (input.resource.read j) (input.length.read j) &&
    BinaryRationalArithmetic.lessEqual (input.length.read j) (input.resource.read j)

def uniformItems {n : ℕ} (input : Input n) : List (Fin n) := (List.finRange n).filter (uniform input)

def fractionalItems {n : ℕ} (input : Input n) : List (Fin n) :=
  (List.finRange n).filter (BinaryResourceState.fractional input.length input.resource)

def pivot {n : ℕ} (input : Input n) : Option (Fin n) := (fractionalItems input).head?

def packed {n : ℕ} (input : Input n) : List (List (Fin n) × SignedWord) :=
  BinaryGreedyPacking.packedGroups input.length.read input.budget (uniformItems input)

def groups {n : ℕ} (input : Input n) : List (List (Fin n)) := (packed input).map Prod.fst

theorem uniform_iff {n : ℕ} (input : Input n) (hC : input.Canonical) (j : Fin n) :
    uniform input j = true ↔ value (input.resource.read j) = value (input.length.read j) := by
  rw [uniform,Bool.and_eq_true,
    BinaryRationalArithmetic.lessEqual_iff _ _ (hC.2.2 j).1 (hC.2.1 j).1,
    BinaryRationalArithmetic.lessEqual_iff _ _ (hC.2.1 j).1 (hC.2.2 j).1]
  exact ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨h.le,h.symm.le⟩⟩

theorem uniformItems_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : uniformItems input = source.uniformItems := by
  unfold uniformItems RationalTerminalLotto.uniformItems
  apply congrArg (List.filter · (List.finRange n))
  funext j
  apply Bool.eq_iff_iff.mpr
  rw [uniform_iff input hC j,hr.2.2 j,hr.2.1 j,decide_eq_true_eq]

theorem fractionalItems_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : fractionalItems input = source.fractionalItems := by
  unfold fractionalItems RationalTerminalLotto.fractionalItems
  apply congrArg (List.filter · (List.finRange n))
  funext j
  apply Bool.eq_iff_iff.mpr
  rw [BinaryResourceState.fractional_iff _ _ hC.2.1 hC.2.2 j,hr.2.2 j,hr.2.1 j,decide_eq_true_eq]

theorem pivot_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : pivot input = source.pivot := by
  rw [pivot,RationalTerminalLotto.pivot,fractionalItems_refines input source hC hr]

theorem packed_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) :
    BinaryGreedyPacking.interpreted (packed input) = rationalPackedGroups source.length source.B source.uniformItems := by
  rw [packed,BinaryGreedyPacking.packedGroups_refines input.length.read input.budget hC.2.1 hC.1]
  have hl : (fun j => value (input.length.read j)) = source.length := funext hr.2.1
  rw [hl,hr.1,uniformItems_refines input source hC hr]

theorem groups_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : groups input = source.groups := by
  have he := congrArg (List.map Prod.fst) (packed_refines input source hC hr)
  rw [rationalPackedGroups_groups] at he
  simpa only [BinaryGreedyPacking.interpreted,List.map_map,Function.comp_def,groups,RationalTerminalLotto.groups] using he

theorem groups_count {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : (groups input).length=2 ∨ (groups input).length=3 := by
  rw [groups_refines input source hC hr]
  exact source.groups_count

theorem packed_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) :
    ∀ entry ∈ packed input, CanonicalWord entry.2 :=
  BinaryGreedyPacking.packedGroups_canonical input.length.read input.budget hC.2.1 _

theorem packed_totals {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) :
    ∀ entry ∈ packed input, value entry.2 = rationalGroupLength source.length entry.1 := by
  have he := BinaryGreedyPacking.packedGroups_totals input.length.read input.budget hC.2.1 hC.1 (uniformItems input)
  have hl : (fun j => value (input.length.read j))=source.length := funext hr.2.1
  simpa only [packed,hl] using he

end Blotto.BinaryTerminalGrouping
