import Blotto.NativeBinarySegmentSampler
import Blotto.BinaryCategoricalFallback
import Blotto.WordMappedIndexedRefinement
import Blotto.WordMachineLowerLeaf

/-! Stored segment programs execute source-free indexed categorical selection,
selected interpolation and exact syntactic lower-leaf fallback. All sizes and
zero-weight slots are retained; source descriptors appear only in proofs. -/

namespace Blotto.BinaryStoredSegmentProgram
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment

structure Prepared (n k : ℕ) where
  table : Segment n k
  canonical : table.Canonical
  nonnegative : ∀ slot, 0 ≤ value (table.weight.read slot)

noncomputable def sourceRow {n : ℕ} (row : FixedArrayTable n SignedWord) : Fin n → ℚ := fun j => value (row.read j)

namespace Prepared

def selectIndexed {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    Option (Fin k) × ℕ :=
  BinaryCategoricalRun.runIndexed fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp

def runIndexed {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool)
    (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable n SignedWord) × ℕ :=
  let selected := prepared.selectIndexed fallback N bits pos hp
  (selected.1.map (fun slot => BinarySegmentPoint.sample prepared.table slot K scalar),selected.2)

def lowerLeaf {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool) : FixedArrayTable n SignedWord :=
  BinarySegmentPoint.sample prepared.table
    (BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative fallback) K scalar

def sample {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FixedArrayTable n SignedWord :=
  match (prepared.runIndexed fallback K N scalar bits 0 (Nat.zero_le N)).1 with
  | some row => row
  | none => prepared.lowerLeaf fallback K scalar

theorem selectIndexed_refines {n k : ℕ} (prepared : Prepared n k) (source : RationalSegmentLottery n k)
    (hr : prepared.table.Refines source) (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    prepared.selectIndexed fallback N bits pos hp = (categoricalMachine fallback).runCursorIndexed N bits (.state source.start) pos hp :=
  BinarySegmentCategorical.selectIndexed_refines prepared.table source prepared.canonical hr fallback N bits pos hp

theorem runIndexed_refines {n k : ℕ} (prepared : Prepared n k) (source : RationalSegmentLottery n k)
    (hr : prepared.table.Refines source) (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((prepared.runIndexed fallback K N scalar bits pos hp).1.map sourceRow,(prepared.runIndexed fallback K N scalar bits pos hp).2) =
      (source.machine fallback K scalar).runCursorIndexed N bits (.state source.start) pos hp := by
  unfold runIndexed
  rw [prepared.selectIndexed_refines source hr]
  unfold RationalSegmentLottery.machine
  rw [WordMappedIndexedRefinement.indexed_refines]
  simp only [Option.map_map,Function.comp_def,WordMappedIndexedRefinement.mapResult]
  apply Prod.ext
  · apply congrArg (fun f => ((categoricalMachine fallback).runCursorIndexed N bits (.state source.start) pos hp).1.map f)
    funext slot j
    exact BinarySegmentPoint.sample_value prepared.table source prepared.canonical hr slot K scalar j
  · rfl

theorem lowerLeaf_value {n k : ℕ} (prepared : Prepared n k) (source : RationalSegmentLottery n k)
    (hr : prepared.table.Refines source) (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool) (j : Fin n) :
    value ((prepared.lowerLeaf fallback K scalar).read j) = (source.machine fallback K scalar).chooseLeaf source.start j := by
  have he := BinarySegmentPoint.sample_value prepared.table source prepared.canonical hr
    (BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative fallback) K scalar j
  have hs := BinaryCategoricalFallback.segment_refines prepared.table source prepared.canonical prepared.nonnegative hr fallback
  have hp := congrArg (fun slot => source.point K slot scalar j) hs
  have hl := WordStateMachine.mapped_chooseLeaf (categoricalMachine fallback) (fun slot => source.point K slot scalar) source.start
  exact he.trans (hp.trans (congrFun hl.symm j))

theorem sample_value {n k : ℕ} (prepared : Prepared n k) (source : RationalSegmentLottery n k)
    (hr : prepared.table.Refines source) (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin n) :
    value ((prepared.sample fallback K N scalar bits).read j) =
      (source.machine fallback K scalar).output N source.start ((source.machine fallback K scalar).chooseLeaf source.start) bits j := by
  have he := congrArg Prod.fst (prepared.runIndexed_refines source hr fallback K N scalar bits 0 (Nat.zero_le N))
  change (prepared.runIndexed fallback K N scalar bits 0 (Nat.zero_le N)).1.map sourceRow =
    ((source.machine fallback K scalar).runNumeric N source.start bits).1 at he
  rw [← WordStateMachine.run_eq_numeric] at he
  unfold sample WordStateMachine.output
  cases hn : (prepared.runIndexed fallback K N scalar bits 0 (Nat.zero_le N)).1 with
  | none =>
    rw [hn,Option.map_none] at he
    rw [← he]
    exact prepared.lowerLeaf_value source hr fallback K scalar j
  | some row =>
    rw [hn,Option.map_some] at he
    rw [← he]
    rfl

theorem sample_canonical {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((prepared.sample fallback K N scalar bits).read j) := by
  unfold sample runIndexed
  dsimp only
  cases hs : (prepared.selectIndexed fallback N bits 0 (Nat.zero_le N)).1 with
  | none => exact BinarySegmentPoint.sample_canonical prepared.table _ K scalar prepared.canonical
  | some slot => exact BinarySegmentPoint.sample_canonical prepared.table slot K scalar prepared.canonical

end Prepared
end Blotto.BinaryStoredSegmentProgram
