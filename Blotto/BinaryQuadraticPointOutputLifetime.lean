import Blotto.BinaryScalarTape
import Blotto.BinaryQuadraticPointLifetime
import Blotto.BinaryQuadraticOutputLifetime

/-! A joined actual selected point-to-original-budget-frame lifetime trace.
One produced midpoint/coordinate array flows directly into quadratic scaling
and Boolean coordinate framing. All old/new regions stay live. Actual source
endpoint heights and the stored budget derive every reservation bound; table,
budget, header and original seed remain explicitly borrowed. Selection and
preceding factory/cache/input lifetimes belong to the enclosing caller. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticPointOutputLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment

def runWithTrace {n k : ℕ} (budget : SignedWord) (header : List Bool) (table : Segment n k)
    (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) : List Bool×Trace :=
  let row := BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits
  let framed := BinaryQuadraticOutputLifetime.outputWithTrace budget header row.1
  (framed.1,[.frames 2,.arrayAllocation 8] ++ under 2 row.2 ++ under 2 framed.2)

@[simp] theorem runWithTrace_erases {n k : ℕ} (budget : SignedWord) (header : List Bool) (table : Segment n k)
    (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (runWithTrace budget header table slot K bits).1=
      BinaryQuadraticOutputLifetime.outputData budget header (BinaryPRGWordControllerSegment.point table slot K bits) := by
  simp only [runWithTrace,BinaryQuadraticOutputLifetime.outputWithTrace_erases,
    BinaryQuadraticPointLifetime.sampleWithTrace_erases,BinaryQuadraticPointLifetime.pointData_controller]

def rowWidth (s K : ℕ) : ℕ := 1+2*expressionHeightBudget (max s (K+2)) 3
def widthBound (budget : SignedWord) (s K : ℕ) : ℕ := max (width budget) (rowWidth s K)
def bound (n s K W headerLength : ℕ) : ℕ :=
  BinaryQuadraticPointLifetime.bound n s K+BinaryQuadraticOutputLifetime.bound n W headerLength+8
def frames (n s K W headerLength : ℕ) : ℕ :=
  BinaryQuadraticPointLifetime.frames n s K+BinaryQuadraticOutputLifetime.frames n W headerLength+4

theorem point_width {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    ∀ j,width ((BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits).1.read j)≤rowWidth s K := by
  intro j
  rw [BinaryQuadraticPointLifetime.sampleWithTrace_state table hC]
  simp only [BinarySegmentPoint.sample,BinarySegmentPoint.atScalar,FixedArrayTable.read_ofFn]
  apply BinarySegmentPoint.interpolate_width _ _ _ (hC.2.1 slot j) (hC.2.2 slot j)
    (BinaryDyadicMidpoint.sample_canonical K bits) (max s (K+2)) (by omega)
  · exact ((hH slot j).1).mono (le_max_left _ _)
  · exact ((hH slot j).2).mono (le_max_left _ _)
  · rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right _ _)

theorem runWithTrace_bounds {n k : ℕ} (budget : SignedWord) (header : List Bool) (table : Segment n k)
    (hB : BinaryRationalOpcode.Valid budget) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    listCells (runWithTrace budget header table slot K bits).2+arraySlots (runWithTrace budget header table slot K bits).2≤
      bound n s K (widthBound budget s K) header.length ∧
    framePeak (runWithTrace budget header table slot K bits).2≤frames n s K (widthBound budget s K) header.length := by
  have hPoint := BinaryQuadraticPointLifetime.sampleWithTrace_bounds table hC s hs hH slot K bits
  have hCanonical : ∀ j,CanonicalWord ((BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits).1.read j) := by
    rw [BinaryQuadraticPointLifetime.sampleWithTrace_state table hC]
    exact BinarySegmentPoint.sample_canonical table slot K bits hC
  have hWidths := point_width table hC s hs hH slot K bits
  have hOutput := BinaryQuadraticOutputLifetime.outputWithTrace_bounds budget header
    (BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits).1 hB (fun j => (hCanonical j).1)
    (widthBound budget s K) (le_max_left _ _) (fun j => (hWidths j).trans (le_max_right _ _))
  have hPointFrames := framePeak_under 2 (BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits).2
  have hOutputFrames := framePeak_under 2 (BinaryQuadraticOutputLifetime.outputWithTrace budget header
    (BinaryQuadraticPointLifetime.sampleWithTrace table slot K bits).1).2
  unfold runWithTrace bound frames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem all_prefix_heap {n k : ℕ} (budget : SignedWord) (header : List Bool) (table : Segment n k)
    (hB : BinaryRationalOpcode.Valid budget) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload budget+header.length+
      BinaryQuadraticPointLifetime.tableCells table+originalSeedCells+borrowedOtherCells)
      (runWithTrace budget header table slot K bits).2 steps≤
      BinaryRationalOpcodeAllocation.payload budget+header.length+BinaryQuadraticPointLifetime.tableCells table+
        originalSeedCells+borrowedOtherCells+bound n s K (widthBound budget s K) header.length :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (runWithTrace_bounds budget header table hB hC s hs hH slot K bits).1

theorem all_prefix_frames {n k : ℕ} (budget : SignedWord) (header : List Bool) (table : Segment n k)
    (hB : BinaryRationalOpcode.Valid budget) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) (steps : ℕ) :
    framePeak ((runWithTrace budget header table slot K bits).2.take steps)≤frames n s K (widthBound budget s K) header.length :=
  (framePeak_take_le _ _).trans (runWithTrace_bounds budget header table hB hC s hs hH slot K bits).2

end Blotto.BinaryQuadraticPointOutputLifetime
