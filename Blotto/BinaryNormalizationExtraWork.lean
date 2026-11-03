import Blotto.BinaryPhysicalPointMeasured
import Blotto.BinaryResourceTraceLength
import Blotto.BinaryNormalizedCoordinate

/-! Division/emission extras of actual planned opcodes and complete affine
interpolation call sequences fit the preceding returned source work. These
observers are never selected producers. Native counter/reference/allocator and
full physical models remain separate. -/
namespace Blotto.BinaryNormalizationExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryWordObjectArray (Store)
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.extra
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem work_lower (op : RealArithmeticOp) (first second : SignedWord) :
    5 ≤ (BinaryPlannedQuadratic.apply op first second).2 := by
  rw [BinaryPlannedQuadratic.apply_previous]
  have h := BinaryResourceTraceLength.canonicalize_work_lower
    (BinaryRationalRawMeasured.traced op first second).1.1
  simp only [BinaryQuadraticMeasured.apply,BinaryQuadraticMeasured.applyMeasured]
  omega

theorem trace_length (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryPlannedQuadratic.apply op first second).1.2.length ≤
      6*(BinaryPlannedQuadratic.apply op first second).2 := by
  simpa only [BinaryPlannedQuadratic.apply_previous,BinaryQuadraticMeasured.apply] using
    BinaryResourceTraceLength.opcode_length op first second

theorem extra_le_work (op : RealArithmeticOp) (first second : SignedWord) :
    BinaryPlannedQuadratic.extra op first second ≤ 155*(BinaryPlannedQuadratic.apply op first second).2 := by
  have h := BinaryPlannedQuadratic.extra_bound op first second
  have ht := trace_length op first second
  have hw := work_lower op first second
  omega

theorem opcode_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryNormalizedCoordinate.opcode op first second).2 ≤
      155*(BinaryNormalizedCoordinate.opcode op first second).1.2 := by
  simpa only [BinaryNormalizedCoordinate.opcode_record,BinaryNormalizedCoordinate.opcode_extra] using
    extra_le_work op first second

theorem coordinate_bound (first second scalar : SignedWord) :
    (BinaryNormalizedCoordinate.coordinate first second scalar).2 ≤
      155*(BinaryNormalizedCoordinate.coordinate first second scalar).1.2 := by
  let a := BinaryNormalizedCoordinate.opcode .sub BinaryPRGRecognition.one scalar
  let b := BinaryNormalizedCoordinate.opcode .mul a.1.1.1 first
  let c := BinaryNormalizedCoordinate.opcode .mul scalar second
  let d := BinaryNormalizedCoordinate.opcode .add b.1.1.1 c.1.1.1
  have ha := opcode_bound .sub BinaryPRGRecognition.one scalar
  have hb := opcode_bound .mul a.1.1.1 first
  have hc := opcode_bound .mul scalar second
  have hd := opcode_bound .add b.1.1.1 c.1.1.1
  change a.2 ≤ 155*a.1.2 at ha
  change b.2 ≤ 155*b.1.2 at hb
  change c.2 ≤ 155*c.1.2 at hc
  change d.2 ≤ 155*d.1.2 at hd
  change a.2+b.2+c.2+d.2 ≤ 155*(a.1.2+b.1.2+c.1.2+d.1.2+16)
  omega

theorem coordinate_full (first second scalar : SignedWord) :
    (BinaryPhysicalInterpolationMeasured.coordinate first second scalar).2+
      (BinaryNormalizedCoordinate.coordinate first second scalar).2 ≤
      156*(BinaryPhysicalInterpolationMeasured.coordinate first second scalar).2 := by
  have h := coordinate_bound first second scalar
  simp only [BinaryPhysicalInterpolationMeasured.coordinate]
  omega

def interpolationLoop {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    List (List Bool) → ℕ
  | [] => 0
  | index::indices =>
      let p := BinaryWordObjectArrayAccessMeasured.get first index
      match p.1.1 with
      | none => 0
      | some wordP =>
          let q := BinaryWordObjectArrayAccessMeasured.get second index
          match q.1.1 with
          | none => 0
          | some wordQ => (BinaryNormalizedCoordinate.coordinate wordP wordQ scalar).2+
              interpolationLoop first second scalar indices

theorem interpolationLoop_bound {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) : interpolationLoop first second scalar indices ≤
      155*(BinaryPhysicalInterpolationMeasured.loop first second scalar indices).2 := by
  induction indices with
  | nil => simp only [interpolationLoop,BinaryPhysicalInterpolationMeasured.loop_nil,BinaryPhysicalInterpolationMeasured.loop_cons]; omega
  | cons index indices ih =>
      simp only [interpolationLoop,BinaryPhysicalInterpolationMeasured.loop_nil,BinaryPhysicalInterpolationMeasured.loop_cons]
      cases hp : (BinaryWordObjectArrayAccessMeasured.get first index).1.1 with
      | none => simp only [hp]; omega
      | some p =>
          simp only [hp]
          cases hq : (BinaryWordObjectArrayAccessMeasured.get second index).1.1 with
          | none => simp only [hq]; omega
          | some q =>
              simp only [hq,BinaryPhysicalInterpolationMeasured.coordinate]
              have hc := coordinate_bound p q scalar
              omega

def interpolationRun (scalar : SignedWord) (p q : List SignedWord) : ℕ :=
  let first := BinaryWordObjectArrayMeasured.prepare p
  let second := BinaryWordObjectArrayMeasured.prepare q
  let indices := BooleanArrayIndexMeasured.enumerate p
  interpolationLoop first.1.1 second.1.1 scalar indices.1.1

theorem interpolationRun_bound (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length) :
    interpolationRun scalar p q ≤ 155*(BinaryPhysicalInterpolationMeasured.run scalar p q hLength).2 := by
  have h := interpolationLoop_bound (BinaryWordObjectArrayMeasured.prepare p).1.1
    (BinaryWordObjectArrayMeasured.prepare q).1.1 scalar (BooleanArrayIndexMeasured.enumerate p).1.1
  simp only [interpolationRun,BinaryPhysicalInterpolationMeasured.run_record]
  omega

theorem interpolationRun_full (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (BinaryPhysicalInterpolationMeasured.run scalar p q hLength).2+interpolationRun scalar p q ≤
      156*BinaryPhysicalInterpolationRun.bound p.length W := by
  have he := interpolationRun_bound scalar p q hLength
  have hw := BinaryPhysicalInterpolationMeasured.run_bound scalar p q hLength hT W hW ht hp hq
  omega

def pointStage (p q : List SignedWord) (seed : List Bool) : ℕ :=
  interpolationRun (BinaryMidpointTapeMeasured.sample seed).1.1 p q

theorem pointStage_bound (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length) :
    pointStage p q seed ≤ 155*(BinaryPhysicalPointMeasured.stage p q seed hLength).2 := by
  have h := interpolationRun_bound (BinaryMidpointTapeMeasured.sample seed).1.1 p q hLength
  simp only [pointStage,BinaryPhysicalPointMeasured.stage_record]
  omega

theorem pointStage_full (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length) :
    (BinaryPhysicalPointMeasured.stage p q seed hLength).2+pointStage p q seed ≤
      156*(BinaryPhysicalPointMeasured.stage p q seed hLength).2 := by
  have h := pointStage_bound p q seed hLength
  omega

theorem pointStage_price (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (BinaryPhysicalPointMeasured.stage p q seed hLength).2+pointStage p q seed ≤
      156*BinaryTapePointLifetime.bound p.length W seed.length := by
  have he := pointStage_full p q seed hLength
  have hw := BinaryPhysicalPointMeasured.stage_bound p q seed hLength W hCap hp hq
  omega

def point {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  pointStage (table.P.read slot).data.toList (table.Q.read slot).data.toList bits.bits

theorem point_bound {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) :
    point table slot K bits ≤ 155*(BinaryPhysicalPointMeasured.sample table slot K bits).2 := by
  let p := table.P.read slot
  let q := table.Q.read slot
  have hLength : p.data.toList.length=q.data.toList.length := by
    rw [Array.length_toList,Array.length_toList,p.size,q.size]
  have h := pointStage_bound p.data.toList q.data.toList bits.bits hLength
  dsimp only [p,q] at h
  simp only [point,BinaryPhysicalPointMeasured.sample_record]
  omega

theorem point_price {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (hC : table.Canonical)
    (s : ℕ) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (BinaryPhysicalPointMeasured.sample table slot K bits).2+point table slot K bits ≤
      156*BinaryPhysicalPointMeasured.price n s K := by
  have he := point_bound table slot K bits
  have hw := BinaryPhysicalPointMeasured.sample_work table hC s hH slot K bits
  omega

end Blotto.BinaryNormalizationExtraWork
