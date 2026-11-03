import Blotto.BinaryNestedProfileLifetime

/-! Restore the terminal's three resource coordinates by actual retained
row and endpoint-array construction. The eighteen weights are reused. -/
namespace Blotto.BinaryTerminalPermutationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def rowWithTrace (row : FixedArrayTable 3 SignedWord) (pi : Equiv.Perm (Fin 3)) :
    FixedArrayTable 3 SignedWord × Trace :=
  BinaryNestedResidualLifetime.copyWithTrace 3 (fun j => row.read (pi j))

def rowsWithTrace (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord))
    (pi : Equiv.Perm (Fin 3)) : FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 18 (fun slot => rowWithTrace (rows.read slot) pi)

def permuteWithTrace (table : Segment) (pi : Equiv.Perm (Fin 3)) : Segment × Trace :=
  let first := rowsWithTrace table.P pi
  let second := rowsWithTrace table.Q pi
  (⟨table.weight,first.1,second.1⟩,wrap 32 2 [first.2,second.2])

theorem permuteWithTrace_erasure (table : Segment) (pi : Equiv.Perm (Fin 3)) :
    (permuteWithTrace table pi).1 = BinaryTerminalProfileCompiler.permute table pi := by
  simp only [permuteWithTrace,rowsWithTrace,rowWithTrace,
    BinaryLifetimeArray.build_erases,BinaryNestedResidualLifetime.copyWithTrace_erasure,
    BinaryTerminalProfileCompiler.permute]

theorem rowWithTrace_usage (row : FixedArrayTable 3 SignedWord) (pi : Equiv.Perm (Fin 3)) :
    usage (rowWithTrace row pi).2 ≤ 128 := by
  have h := BinaryNestedResidualLifetime.copyWithTrace_usage 3 (fun j => row.read (pi j))
  exact h.trans (by decide)

theorem rowsWithTrace_usage (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord))
    (pi : Equiv.Perm (Fin 3)) : usage (rowsWithTrace rows pi).2 ≤ 3200 := by
  have hEach := fun slot => rowWithTrace_usage (rows.read slot) pi
  have ha := array_usage 18 (fun slot => rowWithTrace (rows.read slot) pi) 128 128
    (by intro slot; have h := hEach slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hEach slot; unfold usage at h; omega)
  exact ha.trans (by decide)

theorem permuteWithTrace_usage (table : Segment) (pi : Equiv.Perm (Fin 3)) :
    usage (permuteWithTrace table pi).2 ≤ 6600 := by
  have hp := rowsWithTrace_usage table.P pi
  have hq := rowsWithTrace_usage table.Q pi
  have hw := wrap_usage 32 2 [(rowsWithTrace table.P pi).2,(rowsWithTrace table.Q pi).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [(rowsWithTrace table.P pi).2,(rowsWithTrace table.Q pi).2]) ≤ _
  omega

theorem all_prefix (table : Segment) (pi : Equiv.Perm (Fin 3)) (borrowed steps : ℕ) :
    retainedHeap borrowed (permuteWithTrace table pi).2 steps ≤ borrowed + 6600 ∧
    framePeak ((permuteWithTrace table pi).2.take steps) ≤ 6600 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (permuteWithTrace_usage table pi) borrowed steps

end Blotto.BinaryTerminalPermutationLifetime
