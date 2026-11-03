import Blotto.BinaryNestedReferenceMeasured
import Blotto.BinaryTerminalPermutationLifetime

/-! Actual measured row and endpoint-array packing restores the terminal
coordinate permutation, reusing all eighteen weights. Native indexing and
reference-bit transport retain their separate model obligations. -/
namespace Blotto.BinaryTerminalPermutationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 700000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def row (values : FixedArrayTable 3 SignedWord) (pi : Equiv.Perm (Fin 3)) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 3 (fun j => values.read (pi j))

def rows (values : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) (pi : Equiv.Perm (Fin 3)) :
    (FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build 18 (fun slot => row (values.read slot) pi)

def permute (table : Segment) (pi : Equiv.Perm (Fin 3)) : (Segment × Trace) × ℕ :=
  let first := rows table.P pi
  let second := rows table.Q pi
  ((⟨table.weight,first.1.1,second.1.1⟩,wrap 32 2 [first.1.2,second.1.2]),first.2+second.2+8)

theorem row_data (values : FixedArrayTable 3 SignedWord) (pi : Equiv.Perm (Fin 3)) :
    (row values pi).1.1 = (BinaryTerminalPermutationLifetime.rowWithTrace values pi).1 := by
  simp only [row,BinaryThreeReferenceMeasured.references_data,BinaryTerminalPermutationLifetime.rowWithTrace,
    BinaryNestedResidualLifetime.copyWithTrace_erasure]

theorem rows_data (values : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) (pi : Equiv.Perm (Fin 3)) :
    (rows values pi).1.1 = (BinaryTerminalPermutationLifetime.rowsWithTrace values pi).1 := by
  simp only [rows,BinaryTerminalPermutationLifetime.rowsWithTrace,BinaryLifetimeArrayMeasured.build_data,
    BinaryLifetimeArray.build_erases,row_data]

theorem permute_data (table : Segment) (pi : Equiv.Perm (Fin 3)) :
    (permute table pi).1.1 = (BinaryTerminalPermutationLifetime.permuteWithTrace table pi).1 := by
  simp only [permute,BinaryTerminalPermutationLifetime.permuteWithTrace,rows_data]

theorem rows_bounds (values : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) (pi : Equiv.Perm (Fin 3)) :
    (rows values pi).2 ≤ 42000 ∧ usage (rows values pi).1.2 ≤ 24000 := by
  have hw := BinaryLifetimeArrayMeasured.build_work_bound 18 (fun slot => row (values.read slot) pi) 1036
    (fun _ => BinaryThreeReferenceMeasured.references_work 3 _)
  have hu := BinaryLifetimeArrayMeasured.build_bounds 18 (fun slot => row (values.read slot) pi) 617 617
    (by intro slot; have h : usage (row (values.read slot) pi).1.2 ≤ 617 := BinaryThreeReferenceMeasured.references_usage 3 _; unfold usage at h; omega)
    (by intro slot; have h : usage (row (values.read slot) pi).1.2 ≤ 617 := BinaryThreeReferenceMeasured.references_usage 3 _; unfold usage at h; omega)
  exact ⟨hw.trans (by decide),hu.trans (by decide)⟩

theorem permute_bounds (table : Segment) (pi : Equiv.Perm (Fin 3)) :
    (permute table pi).2 ≤ 85000 ∧ usage (permute table pi).1.2 ≤ 50000 := by
  have hp := rows_bounds table.P pi
  have hq := rows_bounds table.Q pi
  have hw := wrap_usage 32 2 [(rows table.P pi).1.2,(rows table.Q pi).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change (rows table.P pi).2+(rows table.Q pi).2+8 ≤ _ ∧ usage (wrap 32 2 [_,_]) ≤ _
  exact ⟨by omega,by omega⟩

theorem all_prefix (table : Segment) (pi : Equiv.Perm (Fin 3)) (borrowed steps : ℕ) :
    retainedHeap borrowed (permute table pi).1.2 steps ≤ borrowed+50000 ∧ framePeak ((permute table pi).1.2.take steps) ≤ 50000 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (permute_bounds table pi).2 borrowed steps

end Blotto.BinaryTerminalPermutationMeasured
