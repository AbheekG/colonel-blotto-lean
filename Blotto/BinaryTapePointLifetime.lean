import Blotto.BinaryMidpointTapeLifetime
import Blotto.BinaryPhysicalInterpolationRun

/-! A complete scalar-tape-to-coordinate-list run computes the midpoint once
and passes its actual word to both prepared endpoint heaps and every paired
interpolation. No finite callback or native array is used inside this stage. -/
namespace Blotto.BinaryTapePointLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def sampleWithTrace (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) : List SignedWord × Trace :=
  let midpoint := BinaryMidpointTapeLifetime.sampleWithTrace seed
  let row := BinaryPhysicalInterpolationRun.runWithTrace midpoint.1 p q hLength
  (row.1,wrap 32 2 [midpoint.2,row.2])

theorem sample_state (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (sampleWithTrace p q seed hLength).1 =
      BinaryPhysicalInterpolationRun.coordinates (BinaryDirectDyadicMidpoint.sample seed) p q := by
  simp only [sampleWithTrace,BinaryPhysicalInterpolationRun.run_state,BinaryMidpointTapeLifetime.sample_state]

theorem sample_length (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (sampleWithTrace p q seed hLength).1.length = p.length := by
  rw [sample_state,BinaryPhysicalInterpolationRun.coordinates_length _ _ _ hLength]

def bound (n W K : ℕ) : ℕ := BinaryPhysicalInterpolationRun.bound n W+21*K+128

theorem sample_usage (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    usage (sampleWithTrace p q seed hLength).2 ≤ bound p.length W seed.length := by
  let midpoint := BinaryMidpointTapeLifetime.sampleWithTrace seed
  let row := BinaryPhysicalInterpolationRun.runWithTrace midpoint.1 p q hLength
  have hScalar := BinaryMidpointTapeLifetime.sample_contract seed
  have hRow := BinaryPhysicalInterpolationRun.run_usage midpoint.1 p q hLength hScalar.1.1 W (by omega)
    (hScalar.2.1.trans hCap) hp hq
  have hMidpoint := BinaryMidpointTapeLifetime.sample_bounds seed
  have hMid : usage midpoint.2 ≤ 21*seed.length+58 := by
    change listCells midpoint.2+arraySlots midpoint.2 ≤ _ ∧ framePeak midpoint.2 ≤ _ at hMidpoint
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hw := wrap_usage 32 2 [midpoint.2,row.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (sampleWithTrace p q seed hLength).2 ≤ _ at hw
  change usage row.2 ≤ _ at hRow
  unfold bound
  omega

theorem all_prefix (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace p q seed hLength).2 steps ≤ borrowed+bound p.length W seed.length ∧
      framePeak ((sampleWithTrace p q seed hLength).2.take steps) ≤ bound p.length W seed.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sample_usage p q seed hLength W hCap hp hq) borrowed steps

end Blotto.BinaryTapePointLifetime
