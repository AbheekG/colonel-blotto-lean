import Blotto.BinaryExpressionArithmeticEntryWork
import Blotto.BinaryWordSegmentMeasured

/-! Proof-only entry charges follow the actual four affine operands, paired
physical reads, selected point and output scaling. These component sums are
bounded by their existing traces. Categorical/factory and full native costs
remain separate; no additional producer executes on the selected path. -/
namespace Blotto.BinaryPhysicalArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryWordObjectArray
open BinaryExpressionArithmeticEntryWork (quadratic_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def coordinate (first second scalar : SignedWord) : ℕ :=
  let complement := BinaryQuadraticMeasured.apply .sub BinaryPRGRecognition.one scalar
  let left := BinaryQuadraticMeasured.apply .mul complement.1.1 first
  let right := BinaryQuadraticMeasured.apply .mul scalar second
  BinaryArithmeticEntryWork.raw .sub BinaryPRGRecognition.one scalar+
    BinaryArithmeticEntryWork.raw .mul complement.1.1 first+
    BinaryArithmeticEntryWork.raw .mul scalar second+
    BinaryArithmeticEntryWork.raw .add left.1.1 right.1.1

theorem coordinate_bound (first second scalar : SignedWord) :
    coordinate first second scalar ≤ 2*listCells (BinaryPhysicalInterpolationMeasured.coordinate first second scalar).1.2 := by
  have hc := quadratic_bound .sub BinaryPRGRecognition.one scalar
  have hl := quadratic_bound .mul (BinaryQuadraticMeasured.apply .sub BinaryPRGRecognition.one scalar).1.1 first
  have hr := quadratic_bound .mul scalar second
  have hj := quadratic_bound .add
    (BinaryQuadraticMeasured.apply .mul (BinaryQuadraticMeasured.apply .sub BinaryPRGRecognition.one scalar).1.1 first).1.1
    (BinaryQuadraticMeasured.apply .mul scalar second).1.1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,coordinate,BinaryPhysicalInterpolationMeasured.coordinate,BinaryNormalizedCoordinate.coordinate_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def loop {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) : List (List Bool) → ℕ
  | [] => 0
  | index::indices =>
      match (BinaryWordObjectArrayAccessMeasured.get first index).1.1 with
      | none => 0
      | some p => match (BinaryWordObjectArrayAccessMeasured.get second index).1.1 with
        | none => 0
        | some q => coordinate p q scalar+loop first second scalar indices

theorem loop_bound {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    loop first second scalar indices ≤ 2*listCells (BinaryPhysicalInterpolationMeasured.loop first second scalar indices).1.2 := by
  induction indices with
  | nil => simp only [loop,BinaryPhysicalInterpolationMeasured.loop_nil,BinaryPhysicalInterpolationMeasured.loop_cons,wrap,combine,listCells]; omega
  | cons index indices ih =>
      simp only [BinaryPhysicalInterpolationMeasured.loop_nil,BinaryPhysicalInterpolationMeasured.loop_cons]
      split
      · rename_i hp
        simp only [loop,hp]
        omega
      · rename_i p hp
        split
        · rename_i hq
          simp only [loop,hp,hq]
          omega
        · rename_i q hq
          have hc := coordinate_bound p q scalar
          simp only [loop,hp,hq,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
          omega

def interpolate (scalar : SignedWord) (p q : List SignedWord) : ℕ :=
  loop (BinaryWordObjectArrayMeasured.prepare p).1.1 (BinaryWordObjectArrayMeasured.prepare q).1.1 scalar
    (BooleanArrayIndexMeasured.enumerate p).1.1

theorem interpolate_bound (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length) :
    interpolate scalar p q ≤ 2*listCells (BinaryPhysicalInterpolationMeasured.run scalar p q hLength).1.2 := by
  have h := loop_bound (BinaryWordObjectArrayMeasured.prepare p).1.1 (BinaryWordObjectArrayMeasured.prepare q).1.1 scalar
    (BooleanArrayIndexMeasured.enumerate p).1.1
  simp only [interpolate,BinaryPhysicalInterpolationMeasured.run_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def pointStage (p q : List SignedWord) (bits : List Bool) : ℕ :=
  interpolate (BinaryMidpointTapeMeasured.sample bits).1.1 p q

theorem pointStage_bound (p q : List SignedWord) (bits : List Bool) (hLength : p.length=q.length) :
    pointStage p q bits ≤ 2*listCells (BinaryPhysicalPointMeasured.stage p q bits hLength).1.2 := by
  have h := interpolate_bound (BinaryMidpointTapeMeasured.sample bits).1.1 p q hLength
  simp only [pointStage,BinaryPhysicalPointMeasured.stage_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def point {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k) (K : ℕ)
    (bits : BinaryScalarTape K) : ℕ := pointStage (table.P.read slot).data.toList (table.Q.read slot).data.toList bits.bits

theorem point_bound {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k) (K : ℕ)
    (bits : BinaryScalarTape K) : point table slot K bits ≤ 2*listCells (BinaryPhysicalPointMeasured.sample table slot K bits).1.2 := by
  have hLength : (table.P.read slot).data.toList.length=(table.Q.read slot).data.toList.length := by
    rw [Array.length_toList,Array.length_toList,(table.P.read slot).size,(table.Q.read slot).size]
  have h := pointStage_bound (table.P.read slot).data.toList (table.Q.read slot).data.toList bits.bits hLength
  simp only [point,BinaryPhysicalPointMeasured.sample_record,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def segment {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : ℕ :=
  match (BinaryWordSegmentMeasured.select seed prepared fallback pc hp).1.1.1 with
  | none => 0
  | some slot => point prepared.table slot K scalar

theorem segment_bound {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : segment seed prepared fallback K scalar pc hp ≤
      2*listCells (BinaryWordSegmentMeasured.run seed prepared fallback K scalar pc hp).1.2 := by
  simp only [BinaryWordSegmentMeasured.run_record]
  split
  · rename_i hNone
    simp only [segment,hNone]
    omega
  · rename_i slot hSome
    have h := point_bound prepared.table slot K scalar
    simp only [segment,hSome,wrap,combine,listCells_append,listCells_under,listCells]
    omega

def outputEmit {n : ℕ} (store : Store n) (budget : SignedWord) : List (List Bool) → ℕ
  | [] => 0
  | index::indices =>
      match (BinaryWordObjectArrayAccessMeasured.get store index).1.1 with
      | none => 0
      | some word => BinaryArithmeticEntryWork.raw .mul budget word+outputEmit store budget indices

theorem outputEmit_bound {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    outputEmit store budget indices ≤ 2*listCells (BinaryPhysicalOutputMeasured.emit store budget indices).1.2 := by
  induction indices with
  | nil => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,outputEmit,BinaryPhysicalOutputMeasured.emit_nil,BinaryPhysicalOutputMeasured.emit_cons,wrap,combine,listCells]; omega
  | cons index indices ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryPhysicalOutputMeasured.emit_nil,BinaryPhysicalOutputMeasured.emit_cons]
      split
      · rename_i hNone
        simp only [outputEmit,hNone]
        omega
      · rename_i word hSome
        have h := quadratic_bound .mul budget word
        simp only [outputEmit,hSome]
        split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def output (budget : SignedWord) (words : List SignedWord) : ℕ :=
  outputEmit (BinaryWordObjectArrayMeasured.prepare words).1.1 budget (BooleanArrayIndexMeasured.enumerate words).1.1

theorem output_bound (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    output budget words ≤ 2*listCells (BinaryPhysicalOutputMeasured.output budget header words).1.2 := by
  have h := outputEmit_bound (BinaryWordObjectArrayMeasured.prepare words).1.1 budget
    (BooleanArrayIndexMeasured.enumerate words).1.1
  simp only [output,BinaryPhysicalOutputMeasured.output_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem output_with_work (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    let produced := BinaryPhysicalOutputMeasured.output budget header words
    output budget words+produced.2 ≤ 2*(listCells produced.1.2+produced.2) := by
  have h := output_bound budget header words
  dsimp only
  omega

end Blotto.BinaryPhysicalArithmeticEntryWork
