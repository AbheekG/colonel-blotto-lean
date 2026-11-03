import Blotto.BinaryCategoricalRunWork
import Blotto.BinaryStoredSegmentProgram

/-! Actual native stored-segment selection inherits its common denominator
from the supplied canonical table. A normalized source supplies unit mass and
source-derived heights, rather than a reached-cursor or probability-word
oracle. The denominator is a proof measurement, never runtime sampler data.
The work price covers primitive preparation/padding/coin work; table/list
metadata, allocation and physical compiler costs remain separate. -/

namespace Blotto.BinaryStoredSegmentChoiceWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryCategoricalPreparation BinaryCategoricalUnitLattice BinaryCategoricalRunWork
open scoped BigOperators

noncomputable def denominator {n k : ℕ} (table : Segment n k) : ℕ :=
  ∏ slot, (value (table.weight.read slot)).den

theorem denominator_positive {n k : ℕ} (table : Segment n k) : 0 < denominator table := by
  unfold denominator
  exact Finset.prod_pos (fun slot _ => (value (table.weight.read slot)).den_pos)

theorem weight_lattice {n k : ℕ} (table : Segment n k) (slot : Fin k) :
    OnRationalLattice (denominator table) (value (table.weight.read slot)) := by
  unfold OnRationalLattice denominator
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ slot)

theorem denominator_width {n k : ℕ} (table : Segment n k) (s : ℕ)
    (h : ∀ slot, RationalHeight (value (table.weight.read slot)) s) :
    binaryWordWidth (denominator table) ≤ 1 + k * s := by
  have hProd := binaryWordWidth_finset_prod (fun slot => (value (table.weight.read slot)).den) Finset.univ
  have hEach : ∀ slot, binaryWordWidth (value (table.weight.read slot)).den ≤ s :=
    fun slot => binaryWordWidth_le_of_lt_pow (h slot).positive (h slot).2
  have hSum : (∑ slot : Fin k, binaryWordWidth (value (table.weight.read slot)).den) ≤ k * s := by
    calc
      _ ≤ ∑ _slot : Fin k, s := Finset.sum_le_sum (fun slot _ => hEach slot)
      _ = k * s := by simp
  exact hProd.trans (Nat.add_le_add_left hSum 1)

theorem source_unit {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) :
    UnitLattice (denominator prepared.table)
      (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) := by
  refine ⟨?_, ?_⟩
  · intro item hi
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
    exact weight_lattice prepared.table slot
  · have hMass := BinarySegmentCategorical.weights_mass prepared.table source prepared.canonical hR
    change value (BinarySegmentCategorical.weights prepared.table source prepared.canonical hR).mass ≤ 1
    rw [hMass]

def selectIndexedWork {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : (Option (Fin k) × ℕ) × ℕ :=
  runIndexed fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp

theorem selectIndexedWork_state {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (selectIndexedWork prepared fallback N bits pos hp).1 = prepared.selectIndexed fallback N bits pos hp :=
  runIndexed_state fallback N bits _ pos hp

def selectionBound (k s remaining : ℕ) : ℕ :=
  let W := 1 + k * s
  let B := 24 * (5 + 8 * W) + 30
  let P := (k + 1) * (12000 * (2 + 2 * W) ^ 3) + 500 * (2 + 2 * W) ^ 2
  (k + 1) * (P + 12 * (6 + 8 * W) + B + 2) + remaining * B + 1

theorem selectIndexedWork_bound {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ)
    (hH : ∀ slot, RationalHeight (source.weight slot) s)
    (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (selectIndexedWork prepared fallback N bits pos hp).2 ≤ selectionBound k s (N - pos) := by
  have hW := denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hH slot)
  have hUnit := source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length = k :=
    List.length_ofFn
  have hRun := runIndexed_bound (denominator prepared.table) (denominator_positive prepared.table) k fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp
    ⟨hUnit, hLength.le⟩
  change (selectIndexedWork prepared fallback N bits pos hp).2 ≤ _ at hRun
  simp only [allowance, hLength] at hRun
  apply hRun.trans
  unfold choiceBound BinaryCategoricalPreparationWork.preparationBound bodyBound selectionBound
  dsimp only
  gcongr

end Blotto.BinaryStoredSegmentChoiceWork
