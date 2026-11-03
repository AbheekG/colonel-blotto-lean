import Blotto.BinarySyntaxLifetime
import Blotto.BinaryLifetimeArray
import Blotto.BinaryDirectDyadicMidpoint
import Blotto.BinaryMidpointTapeLifetime
import Blotto.BinarySegmentPoint

/-! A selected segment point is produced by one direct Boolean midpoint and
the actual interpolation syntax in each coordinate. Midpoint trimming has its
own concrete tape loops and linear trace; interpolation uses the retained Euclidean opcode
allocation backend. Exact old midpoint/coordinate bytes hold. All nested
array prefixes, environment records and child reservations stay live. The
segment/seed/AST input storage is explicitly borrowed. -/
set_option autoImplicit false
namespace Blotto.BinarySegmentPointLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment BinarySegmentPoint

def midpointWithTrace (seed : List Bool) : SignedWord × Trace :=
  BinaryMidpointTapeLifetime.sampleWithTrace seed

@[simp] theorem midpointWithTrace_erases (seed : List Bool) :
    (midpointWithTrace seed).1=BinaryDirectDyadicMidpoint.sample seed :=
  BinaryMidpointTapeLifetime.sample_state seed

theorem midpointWithTrace_bounds (seed : List Bool) :
    listCells (midpointWithTrace seed).2+arraySlots (midpointWithTrace seed).2 ≤ 19*seed.length+50 ∧
    framePeak (midpointWithTrace seed).2 ≤ 2*seed.length+8 :=
  BinaryMidpointTapeLifetime.sample_bounds seed

def sampleWithTrace {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    FixedArrayTable n SignedWord × Trace :=
  let midpoint := midpointWithTrace (List.ofFn bits)
  let row := BinaryLifetimeArray.build n (fun j =>
    BinarySyntaxLifetime.runWithTrace (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j) midpoint.1) program)
  (row.1,[.frames (K+8),.listAllocation K,.arrayAllocation (8*n+8)] ++ under 2 midpoint.2 ++ under 2 row.2)

@[simp] theorem sampleWithTrace_erases {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    (sampleWithTrace table slot K bits).1=BinarySegmentPoint.sample table slot K bits := by
  simp only [sampleWithTrace,BinaryLifetimeArray.build_erases,BinarySyntaxLifetime.runWithTrace_erases,
    midpointWithTrace_erases,BinaryDirectDyadicMidpoint.sample_ofFn,BinarySegmentPoint.sample,BinarySegmentPoint.atScalar,
    BinarySegmentPoint.interpolate]

def bound (n s K : ℕ) : ℕ :=
  20*K+50+n*BinarySyntaxLifetime.bound 9 9 (max s (K+2)) 3+2*(n+1)^2+8*n+16

theorem program_sizes : program.nodes ≤ 9 ∧ program.rational.operationBound ≤ 9 ∧ program.rational.depth ≤ 3 := by decide

theorem environment_height (first second scalar : SignedWord) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hScalar : RationalHeight (value scalar) s) : BinarySyntaxUniformWork.EnvHeight (BinarySegmentPoint.environment first second scalar) s := by
  intro j
  simp only [BinarySegmentPoint.environment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact hFirst
  · exact hSecond
  · exact hScalar

theorem sampleWithTrace_bounds {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    listCells (sampleWithTrace table slot K bits).2+arraySlots (sampleWithTrace table slot K bits).2 ≤ bound n s K ∧
    framePeak (sampleWithTrace table slot K bits).2 ≤ n+2*K+33 := by
  let scalar := (midpointWithTrace (List.ofFn bits)).1
  let source := fun j : Fin n => BinarySyntaxLifetime.runWithTrace
    (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j) scalar) program
  have he : scalar=BinaryDyadicMidpoint.sample K bits := by
    dsimp only [scalar]; rw [midpointWithTrace_erases,BinaryDirectDyadicMidpoint.sample_ofFn]
  have hScalar : CanonicalWord scalar := by rw [he]; exact BinaryDyadicMidpoint.sample_canonical K bits
  have hHeight : RationalHeight (value scalar) (max s (K+2)) := by
    rw [he,BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right _ _)
  have hEach := fun j => BinarySyntaxLifetime.runWithTrace_bounds
    (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j) scalar) program
    (environment_canonical _ _ _ (hC.2.1 slot j) (hC.2.2 slot j) hScalar)
    (max s (K+2)) 3 9 9 (hs.trans (le_max_left _ _))
    (environment_height _ _ _ _ ((hH slot j).1.mono (le_max_left _ _))
      ((hH slot j).2.mono (le_max_left _ _)) hHeight) program_sizes.2.2 program_sizes.2.1 program_sizes.1
  have hRow := BinaryLifetimeArray.build_bounds n source
    (BinarySyntaxLifetime.bound 9 9 (max s (K+2)) 3) 17
    (fun j => (hEach j).1) (fun j => (hEach j).2)
  have hMidpoint := midpointWithTrace_bounds (List.ofFn bits)
  simp only [List.length_ofFn] at hMidpoint
  have hMidpointFrames := framePeak_under 2 (midpointWithTrace (List.ofFn bits)).2
  have hRowFrames := framePeak_under 2 (BinaryLifetimeArray.build n source).2
  unfold sampleWithTrace bound
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  dsimp only [source,scalar] at hRow hRowFrames
  exact ⟨by omega,by omega⟩

theorem sample_all_prefix {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (sampleWithTrace table slot K bits).2 steps ≤ borrowedCells+bound n s K := by
  have hb := (sampleWithTrace_bounds table hC s hs hH slot K bits).1
  have hl := listCells_take_le (sampleWithTrace table slot K bits).2 steps
  have ha := arraySlots_take_le (sampleWithTrace table slot K bits).2 steps
  unfold retainedHeap
  omega

end Blotto.BinarySegmentPointLifetime
