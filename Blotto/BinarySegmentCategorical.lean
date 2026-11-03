import Blotto.BinaryCategoricalRun
import Blotto.RationalSegmentMachine

/-! Segment selection reads the stored weight array into indexed labels, then
uses the native Boolean categorical controller at its caller's current reader
position. Descriptor zero weights and duplicate rows retain their slots. -/

namespace Blotto.BinarySegmentCategorical
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryCategoricalPreparation
open scoped BigOperators

def weights {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) : WeightList (Fin k) where
  items:=List.ofFn (fun i=>(i,segment.weight.read i))
  canonical:=by
    intro item hi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
    exact hCanonical.1 i
  nonnegative:=by
    intro item hi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
    rw [hRefines.1 i]
    exact source.nonnegative i

theorem weights_reference {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) :
    (weights segment source hCanonical hRefines).reference=rationalWeightList source.weight source.nonnegative:=by
  have hItems : (weights segment source hCanonical hRefines).reference.items=
      (rationalWeightList source.weight source.nonnegative).items:=by
    simp only [WeightList.reference,weights,rationalWeightList,List.map_ofFn]
    congr 1
    funext i
    change (i,value (segment.weight.read i))=(i,source.weight i)
    rw [hRefines.1 i]
  cases hLeft : (weights segment source hCanonical hRefines).reference with
  | mk items nonnegative=>
      cases hRight : rationalWeightList source.weight source.nonnegative with
      | mk target targetNonnegative=>
          rw [hLeft,hRight] at hItems
          dsimp only at hItems
          subst target
          rfl

theorem weights_mass {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) :
    value (weights segment source hCanonical hRefines).mass=1:=by
  rw [WeightList.mass_value,weights_reference,rationalWeightList_mass,source.mass]

def selectIndexed {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) : Option (Fin k)×ℕ:=
  BinaryCategoricalRun.runIndexed fallback N bits (.remaining (weights segment source hCanonical hRefines)) pos hpos

def select {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) : Option (Fin k)×ℕ:=
  selectIndexed segment source hCanonical hRefines fallback N bits 0 (Nat.zero_le N)

def output {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) : Fin k:=
  (select segment source hCanonical hRefines fallback N bits).1.getD fallback

theorem selectIndexed_refines {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) :
    selectIndexed segment source hCanonical hRefines fallback N bits pos hpos=
      (categoricalMachine fallback).runCursorIndexed N bits (.state source.start) pos hpos:=by
  rw [selectIndexed,BinaryCategoricalRun.runIndexed_refines,BinaryCategoricalRun.Cursor.reference,weights_reference]
  rfl

theorem select_refines {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) :
    select segment source hCanonical hRefines fallback N bits=(categoricalMachine fallback).run N source.start bits:=by
  rw [select,selectIndexed_refines,WordStateMachine.run_eq_numeric]
  rfl

theorem selectIndexed_position {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) :
    pos≤(selectIndexed segment source hCanonical hRefines fallback N bits pos hpos).2 ∧
      (selectIndexed segment source hCanonical hRefines fallback N bits pos hpos).2≤N:=
  BinaryCategoricalRun.runIndexed_position fallback N bits (.remaining _) pos hpos

theorem output_refines {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k)
    (hCanonical : segment.Canonical) (hRefines : segment.Refines source) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) :
    output segment source hCanonical hRefines fallback N bits=source.choose fallback N bits:=by
  unfold output RationalSegmentLottery.choose WordStateMachine.output
  rw [select_refines]

end Blotto.BinarySegmentCategorical
