import Blotto.BinaryNestedFirstGeometryLifetime
import Blotto.BinaryQuadraticThreeFactoryLifetime

/-! Retained zero-probability corner and actual third-coordinate translation
for the first nested conditional descriptor. -/
namespace Blotto.BinaryNestedFirstAssemblyLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def cornerWithTrace (input : Input) (x : SignedWord) : Segment × Trace :=
  let weights := BinaryThreeReferenceLifetime.weightsWithTrace
  let first := BinaryThreeReferenceLifetime.rowsWithTrace BinaryRationalOpcode.zero input.d x
  let second := BinaryThreeReferenceLifetime.rowsWithTrace input.a BinaryRationalOpcode.zero x
  (⟨weights.1,first.1,second.1⟩,wrap 32 2 [weights.2,first.2,second.2])

theorem cornerWithTrace_erasure (input : Input) (x : SignedWord) :
    (cornerWithTrace input x).1 = BinaryNestedFirstConditional.corner input x := by
  rfl

theorem cornerWithTrace_usage (input : Input) (x : SignedWord) :
    usage (cornerWithTrace input x).2 ≤ 4096 := by
  have hwg := BinaryThreeReferenceLifetime.weightsWithTrace_usage
  have hp := BinaryThreeReferenceLifetime.rowsWithTrace_usage BinaryRationalOpcode.zero input.d x
  have hq := BinaryThreeReferenceLifetime.rowsWithTrace_usage input.a BinaryRationalOpcode.zero x
  have hw := wrap_usage 32 2
    [BinaryThreeReferenceLifetime.weightsWithTrace.2,
      (BinaryThreeReferenceLifetime.rowsWithTrace BinaryRationalOpcode.zero input.d x).2,
      (BinaryThreeReferenceLifetime.rowsWithTrace input.a BinaryRationalOpcode.zero x).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [BinaryThreeReferenceLifetime.weightsWithTrace.2,
      (BinaryThreeReferenceLifetime.rowsWithTrace BinaryRationalOpcode.zero input.d x).2,
      (BinaryThreeReferenceLifetime.rowsWithTrace input.a BinaryRationalOpcode.zero x).2]) ≤ _
  omega

def rowShiftWithTrace (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    FixedArrayTable 3 SignedWord × Trace :=
  let added := BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x
  let built := BinaryThreeReferenceLifetime.rowWithTrace (row.read 0) (row.read 1) added.1
  (built.1,wrap 24 2 [added.2,built.2])

theorem rowShiftWithTrace_erasure (row : FixedArrayTable 3 SignedWord) (x : SignedWord)
    (hRow : CanonicalWord (row.read 2)) (hX : CanonicalWord x) :
    (rowShiftWithTrace row x).1 = FixedArrayTable.ofFn ![row.read 0,row.read 1,
      BinaryRationalOpcode.apply .add (row.read 2) x] := by
  simp only [rowShiftWithTrace,BinaryThreeReferenceLifetime.rowWithTrace_erasure,
    BinaryQuadraticLifetime.applyWithTrace_state .add _ _ hRow.1 hX.1]

def rowEnvelope (W : ℕ) : ℕ := opcodeEnvelope W + 160

theorem rowShiftWithTrace_usage (row : FixedArrayTable 3 SignedWord) (x : SignedWord)
    (W : ℕ) (hRow : width (row.read 2) ≤ W) (hX : width x ≤ W) :
    usage (rowShiftWithTrace row x).2 ≤ rowEnvelope W := by
  have hAdd := opcode_usage .add (row.read 2) x W hRow hX
  have hBuilt := BinaryThreeReferenceLifetime.rowWithTrace_usage (row.read 0) (row.read 1)
    (BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x).1
  have hw := wrap_usage 24 2
    [(BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x).2,
      (BinaryThreeReferenceLifetime.rowWithTrace (row.read 0) (row.read 1)
        (BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 24 2
    [(BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x).2,
      (BinaryThreeReferenceLifetime.rowWithTrace (row.read 0) (row.read 1)
        (BinaryQuadraticLifetime.applyWithTrace .add (row.read 2) x).1).2]) ≤ _
  unfold rowEnvelope
  omega

def rowsShiftWithTrace (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    FixedArrayTable 9 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 9 (fun slot => rowShiftWithTrace (rows.read slot) x)

theorem rowsShiftWithTrace_erasure (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord))
    (x : SignedWord) (hRows : ∀ slot,CanonicalWord ((rows.read slot).read 2))
    (hX : CanonicalWord x) :
    (rowsShiftWithTrace rows x).1 = FixedArrayTable.ofFn (fun slot =>
      FixedArrayTable.ofFn ![(rows.read slot).read 0,(rows.read slot).read 1,
        BinaryRationalOpcode.apply .add ((rows.read slot).read 2) x]) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro slot
  simp only [rowsShiftWithTrace,BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn]
  exact rowShiftWithTrace_erasure (rows.read slot) x (hRows slot) hX

def rowsEnvelope (W : ℕ) : ℕ := 10 * rowEnvelope W + 256

theorem rowsShiftWithTrace_usage (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord))
    (x : SignedWord) (W : ℕ) (hRows : ∀ slot,width ((rows.read slot).read 2) ≤ W)
    (hX : width x ≤ W) : usage (rowsShiftWithTrace rows x).2 ≤ rowsEnvelope W := by
  have hr := fun slot => rowShiftWithTrace_usage (rows.read slot) x W (hRows slot) hX
  have hArray := array_usage 9 (fun slot => rowShiftWithTrace (rows.read slot) x)
    (rowEnvelope W) (rowEnvelope W)
    (by intro slot; have h := hr slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hr slot; unfold usage at h; omega)
  exact hArray.trans (by unfold rowsEnvelope; omega)

def shiftThirdWithTrace (table : Segment) (x : SignedWord) : Segment × Trace :=
  let first := rowsShiftWithTrace table.P x
  let second := rowsShiftWithTrace table.Q x
  (⟨table.weight,first.1,second.1⟩,wrap 32 2 [first.2,second.2])

theorem shiftThirdWithTrace_erasure (table : Segment) (x : SignedWord)
    (hC : table.Canonical) (hX : CanonicalWord x) :
    (shiftThirdWithTrace table x).1 = BinarySegmentAssembly.shiftThird table x := by
  simp only [shiftThirdWithTrace,BinarySegmentAssembly.shiftThird,
    rowsShiftWithTrace_erasure table.P x (fun slot => hC.2.1 slot 2) hX,
    rowsShiftWithTrace_erasure table.Q x (fun slot => hC.2.2 slot 2) hX]

def shiftEnvelope (W : ℕ) : ℕ := 2 * rowsEnvelope W + 64

theorem shiftThirdWithTrace_usage (table : Segment) (x : SignedWord) (W : ℕ)
    (hP : ∀ slot,width ((table.P.read slot).read 2) ≤ W)
    (hQ : ∀ slot,width ((table.Q.read slot).read 2) ≤ W)
    (hX : width x ≤ W) :
    usage (shiftThirdWithTrace table x).2 ≤ shiftEnvelope W := by
  have hp := rowsShiftWithTrace_usage table.P x W hP hX
  have hq := rowsShiftWithTrace_usage table.Q x W hQ hX
  have hw := wrap_usage 32 2
    [(rowsShiftWithTrace table.P x).2,(rowsShiftWithTrace table.Q x).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(rowsShiftWithTrace table.P x).2,(rowsShiftWithTrace table.Q x).2]) ≤ _
  unfold shiftEnvelope
  omega

end Blotto.BinaryNestedFirstAssemblyLifetime
