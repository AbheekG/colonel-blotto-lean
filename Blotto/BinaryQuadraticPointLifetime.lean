import Blotto.BinaryScalarTape
import Blotto.BinaryQuadraticSyntaxLifetime
import Blotto.BinaryPhysicalPointLifetime
import Blotto.BinarySegmentPointLifetime
import Blotto.BinaryPRGWordControllerSegment

/-! Selected points now execute physical endpoint-heap reads at Boolean
indices and four direct affine opcodes per coordinate. The standalone native
environment/syntax helpers remain reference components. Actual midpoint,
endpoint projections, produced coordinates and final native packing retain
source reservations; native reference-bit and scalar/seed models are separate. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticPointLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment
open scoped BigOperators

def pointData {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) : FixedArrayTable n SignedWord :=
  let scalar := BinaryDirectDyadicMidpoint.sample (List.ofFn bits)
  FixedArrayTable.ofFn (fun j => BinaryQuadraticData.expression
    (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j) scalar)
    BinarySegmentPoint.program.compile)

theorem pointData_state {n k : ℕ} (table : Segment n k) (hC : table.Canonical) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) : pointData table slot K bits=BinarySegmentPoint.sample table slot K bits := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [pointData,BinaryDirectDyadicMidpoint.sample_ofFn,BinarySegmentPoint.sample,BinarySegmentPoint.atScalar,
    FixedArrayTable.read_ofFn,BinarySegmentPoint.interpolate]
  exact BinaryQuadraticData.expression_state _ _
    (fun i => (BinarySegmentPoint.environment_canonical _ _ _ (hC.2.1 slot j) (hC.2.2 slot j)
      (BinaryDyadicMidpoint.sample_canonical K bits) i).1)
    (BinarySegmentPoint.program.compile.canonicalLiterals_valid BinarySegmentPoint.program.compile_canonical)

theorem pointData_controller {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    pointData table slot K bits=BinaryPRGWordControllerSegment.point table slot K bits := by
  simp only [pointData,BinaryPRGWordControllerSegment.point,BinaryPRGWordControllerSegment.interpolate,
    BinaryDirectDyadicMidpoint.sample_ofFn]

def environmentWithTrace (first second scalar : SignedWord) : FixedArrayTable 3 SignedWord×Trace :=
  BinaryLifetimeArray.build 3 (fun j => (![first,second,scalar] j,[.frames 1]))

@[simp] theorem environmentWithTrace_erases (first second scalar : SignedWord) :
    (environmentWithTrace first second scalar).1=BinarySegmentPoint.environment first second scalar := rfl

theorem environmentWithTrace_bounds (first second scalar : SignedWord) :
    listCells (environmentWithTrace first second scalar).2+arraySlots (environmentWithTrace first second scalar).2≤40 ∧
    framePeak (environmentWithTrace first second scalar).2≤10 := by
  exact BinaryLifetimeArray.build_bounds 3 _ 0 1 (by intro j; simp [listCells,arraySlots])
    (by intro j; simp [framePeak])

def coordinateWithTrace (first second scalar : SignedWord) : SignedWord×Trace :=
  let env := environmentWithTrace first second scalar
  let evaluated := BinaryQuadraticSyntaxLifetime.runWithTrace env.1 BinarySegmentPoint.program
  (evaluated.1,[.frames 2,.arrayAllocation 8] ++ under 2 env.2 ++ under 2 evaluated.2)

@[simp] theorem coordinateWithTrace_erases (first second scalar : SignedWord) :
    (coordinateWithTrace first second scalar).1=BinaryQuadraticData.expression
      (BinarySegmentPoint.environment first second scalar) BinarySegmentPoint.program.compile := by
  simp only [coordinateWithTrace,BinaryQuadraticSyntaxLifetime.runWithTrace_erases,environmentWithTrace_erases]

theorem coordinateWithTrace_bounds (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar)
    (s : ℕ) (hs : 3≤s) (hP : RationalHeight (value first) s) (hQ : RationalHeight (value second) s)
    (hT : RationalHeight (value scalar) s) :
    listCells (coordinateWithTrace first second scalar).2+arraySlots (coordinateWithTrace first second scalar).2≤
      BinaryQuadraticSyntaxLifetime.bound 9 9 s 3+48 ∧
    framePeak (coordinateWithTrace first second scalar).2≤BinaryQuadraticSyntaxLifetime.frames 9 s 3+12 := by
  have hEnv := environmentWithTrace_bounds first second scalar
  have hEval := BinaryQuadraticSyntaxLifetime.runWithTrace_bounds
    (BinarySegmentPoint.environment first second scalar) BinarySegmentPoint.program
    (BinarySegmentPoint.environment_canonical _ _ _ hFirst hSecond hScalar) s 3 9 9 hs
    (BinarySegmentPointLifetime.environment_height _ _ _ _ hP hQ hT)
    BinarySegmentPointLifetime.program_sizes.2.2 BinarySegmentPointLifetime.program_sizes.2.1
    BinarySegmentPointLifetime.program_sizes.1
  have hEF := framePeak_under 2 (environmentWithTrace first second scalar).2
  have hVF := framePeak_under 2 (BinaryQuadraticSyntaxLifetime.runWithTrace
    (BinarySegmentPoint.environment first second scalar) BinarySegmentPoint.program).2
  unfold coordinateWithTrace
  simp only [environmentWithTrace_erases,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def sampleWithTrace {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    FixedArrayTable n SignedWord×Trace :=
  BinaryPhysicalPointLifetime.sampleWithTrace table slot K bits

@[simp] theorem sampleWithTrace_erases {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (sampleWithTrace table slot K bits).1=pointData table slot K bits := by
  simpa only [sampleWithTrace,pointData] using BinaryPhysicalPointLifetime.sample_state table slot K bits

theorem sampleWithTrace_state {n k : ℕ} (table : Segment n k) (hC : table.Canonical) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) : (sampleWithTrace table slot K bits).1=BinarySegmentPoint.sample table slot K bits := by
  rw [sampleWithTrace_erases,pointData_state table hC]

def expressionBound (s K : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 9 9 (max s (K+2)) 3
def expressionFrames (s K : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 9 (max s (K+2)) 3
def bound (n s K : ℕ) : ℕ := 20*K+50+n*(expressionBound s K+48)+2*(n+1)^2+16+BinaryPhysicalPointLifetime.bound n s K
def frames (n s K : ℕ) : ℕ := n+2*K+expressionFrames s K+32+BinaryPhysicalPointLifetime.bound n s K

theorem sampleWithTrace_bounds {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    listCells (sampleWithTrace table slot K bits).2+arraySlots (sampleWithTrace table slot K bits).2≤bound n s K ∧
    framePeak (sampleWithTrace table slot K bits).2≤frames n s K := by
  have h := BinaryPhysicalPointLifetime.sample_usage table hC s hs hH slot K bits
  unfold BinaryPRGHeapTraceUsage.usage BinaryPRGHeapPrimitiveLifetime.cells at h
  simp only [sampleWithTrace]
  unfold bound frames
  exact ⟨by omega,by omega⟩

def tableCells {n k : ℕ} (table : Segment n k) : ℕ := 8+4*k+2*n*k+
  (∑ slot,BinaryRationalOpcodeAllocation.payload (table.weight.read slot))+
  (∑ slot,∑ j,(BinaryRationalOpcodeAllocation.payload ((table.P.read slot).read j)+
    BinaryRationalOpcodeAllocation.payload ((table.Q.read slot).read j)))

theorem all_prefix_heap {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (tableCells table+originalSeedCells+borrowedOtherCells) (sampleWithTrace table slot K bits).2 steps≤
      tableCells table+originalSeedCells+borrowedOtherCells+bound n s K :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (sampleWithTrace_bounds table hC s hs hH slot K bits).1

theorem all_prefix_frames {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3≤s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) (steps : ℕ) :
    framePeak ((sampleWithTrace table slot K bits).2.take steps)≤frames n s K :=
  (framePeak_take_le _ _).trans (sampleWithTrace_bounds table hC s hs hH slot K bits).2

end Blotto.BinaryQuadraticPointLifetime
