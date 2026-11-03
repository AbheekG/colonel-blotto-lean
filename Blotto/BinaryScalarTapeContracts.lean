import Blotto.BinaryPRGHeapSeedTableOutputLifetime

/-! Retained cursor tapes and arbitrary-reader compatibility for the adopted
complete path. These are exact-data/source contracts, not host runtime claims. -/
namespace Blotto.BinaryScalarTapeContracts
open RationalLottoResourceSystem

theorem packWithTrace_scalar_tape (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (BinarySeedPreparationSpace.packWithTrace n K choice scalar outer hc hs ho).1.scalarView.bits = scalar := rfl

theorem packWithTrace_outer_tape (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (BinarySeedPreparationSpace.packWithTrace n K choice scalar outer hc hs ho).1.outerView.bits = outer := rfl

def retainedFlat {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) : List Bool :=
  tables.choice.data.toList ++ tables.scalarView.bits ++ tables.outerView.bits

theorem retainedFlat_eq {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) :
    retainedFlat tables = tables.flatList := by
  simp only [retainedFlat,BinaryPRGSeedBlocks.Tables.flatList,
    tables.scalarView.correct,tables.outerView.correct,tables.scalarView_read,tables.outerView_read,
    BinaryPRGSeedBlocks.listOfFn_read]

theorem readWithTrace_retained_seed (n K : ℕ) (seed : List Bool)
    (tables : BinaryPRGSeedBlocks.Tables n K)
    (h : (BinarySeedPreparationSpace.readWithTrace n K seed).1.1 = some tables) :
    retainedFlat tables = seed := by
  rw [BinarySeedPreparationSpace.readWithTrace_result] at h
  rw [retainedFlat_eq]
  exact BinaryPRGSeedBlocks.read_success_flatList n K seed tables h

theorem physical_point_reader_adapter {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k)
    (slot : Fin k) (K : ℕ) (view : BinaryScalarTape K) :
    BinaryPhysicalPointLifetime.sampleWithTrace table slot K (BinaryScalarTape.ofFn view.read) =
      BinaryPhysicalPointLifetime.sampleWithTrace table slot K view := by
  rw [BinaryScalarTape.ofFn_read_eq]

theorem nested_midpoint_reader_adapter (K : ℕ) (view : BinaryScalarTape K) :
    BinaryNestedFirstLocationLifetime.midpointWithTrace K (BinaryScalarTape.ofFn view.read) =
      BinaryNestedFirstLocationLifetime.midpointWithTrace K view := by
  rw [BinaryScalarTape.ofFn_read_eq]

theorem complete_reader_adapter {n : ℕ} (store : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    BinaryPRGPhysicalFramedLifetime.runWithTrace store request rich K
        (BinaryScalarTape.ofFn outer.read) (BinaryScalarTape.ofFn scalar.read) header =
      BinaryPRGPhysicalFramedLifetime.runWithTrace store request rich K outer scalar header := by
  rw [BinaryScalarTape.ofFn_read_eq,BinaryScalarTape.ofFn_read_eq]

end Blotto.BinaryScalarTapeContracts
