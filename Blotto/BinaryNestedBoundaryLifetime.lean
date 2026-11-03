import Blotto.BinaryUnorderedThreeLifetime
import Blotto.BinaryNestedSpecFactoryWork

/-! Actual q=0/q=1 nested profile branches: traced Boolean comparisons,
complete unordered-three descriptors, and retained 18-slot padding arrays. -/
namespace Blotto.BinaryNestedBoundaryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

def padWithTrace (table : BinaryStoredOverlapEnvironment.Segment 3 9) :
    BinaryStoredOverlapEnvironment.Segment 3 18 × Trace :=
  let weights := BinaryLifetimeArray.build 18 (fun slot =>
    (Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot,wrap 8 1 []))
  let P := BinaryLifetimeArray.build 18 (fun slot =>
    (Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot,wrap 8 1 []))
  let Q := BinaryLifetimeArray.build 18 (fun slot =>
    (Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot,wrap 8 1 []))
  (⟨weights.1,P.1,Q.1⟩,wrap 32 2 [weights.2,P.2,Q.2])

theorem padWithTrace_erasure (table : BinaryStoredOverlapEnvironment.Segment 3 9) :
    (padWithTrace table).1 = BinarySegmentAssembly.padRight table 9 0 := by
  simp only [padWithTrace,BinarySegmentAssembly.padRight,BinaryLifetimeArray.build_erases]

theorem padWithTrace_usage (table : BinaryStoredOverlapEnvironment.Segment 3 9) :
    usage (padWithTrace table).2 ≤ 4096 := by
  have hw : usage (BinaryLifetimeArray.build (α := SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot,wrap 8 1 []))).2 ≤ 899 := by
    have h := array_usage (α := SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot,wrap 8 1 [])) 8 1
      (by intro slot; simp [wrap,combine,listCells,arraySlots])
      (by intro slot; simp [wrap,combine,framePeak])
    exact h
  have hp : usage (BinaryLifetimeArray.build (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot,wrap 8 1 []))).2 ≤ 899 := by
    have h := array_usage (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot,wrap 8 1 [])) 8 1
      (by intro slot; simp [wrap,combine,listCells,arraySlots])
      (by intro slot; simp [wrap,combine,framePeak])
    exact h
  have hq : usage (BinaryLifetimeArray.build (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot,wrap 8 1 []))).2 ≤ 899 := by
    have h := array_usage (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot,wrap 8 1 [])) 8 1
      (by intro slot; simp [wrap,combine,listCells,arraySlots])
      (by intro slot; simp [wrap,combine,framePeak])
    exact h
  have hWrap := wrap_usage 32 2
    [(BinaryLifetimeArray.build (α := SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot,wrap 8 1 []))).2,
      (BinaryLifetimeArray.build (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot,wrap 8 1 []))).2,
      (BinaryLifetimeArray.build (α := FixedArrayTable 3 SignedWord) 18 (fun slot =>
      (Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot,wrap 8 1 []))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  unfold padWithTrace
  dsimp only
  omega

def boundaryWithTrace (input : BinaryNestedParameters.Input) :
    Option (BinaryStoredOverlapEnvironment.Segment 3 18) × Trace :=
  let zero := BinaryQuadraticExpressionLifetime.compareWithTrace input.q BinaryRationalOpcode.zero
  if zero.1 then
    let child := BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.longInput input)
    let padded := padWithTrace child.1
    (some padded.1,wrap 32 2 [zero.2,child.2,padded.2])
  else
    let one := BinaryQuadraticExpressionLifetime.compareWithTrace
      BinaryExpressionCompiler.Constant.one.word input.q
    if one.1 then
      let child := BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.shortInput input)
      let padded := padWithTrace child.1
      (some padded.1,wrap 32 2 [zero.2,one.2,child.2,padded.2])
    else (none,wrap 32 2 [zero.2,one.2])

def oldBoundary (input : BinaryNestedParameters.Input) :
    Option (BinaryStoredOverlapEnvironment.Segment 3 18) :=
  if BinaryNestedSpecProfile.qZero input then
    some (BinarySegmentAssembly.padRight
      (BinaryThreeSpecCompiler.descriptor (BinaryNestedSpecProfile.longInput input)) 9 0)
  else if BinaryNestedSpecProfile.qOne input then
    some (BinarySegmentAssembly.padRight
      (BinaryThreeSpecCompiler.descriptor (BinaryNestedSpecProfile.shortInput input)) 9 0)
  else none

theorem boundaryWithTrace_erasure (input : BinaryNestedParameters.Input)
    (hC : input.Canonical) :
    (boundaryWithTrace input).1 = oldBoundary input := by
  unfold boundaryWithTrace oldBoundary BinaryNestedSpecProfile.qZero BinaryNestedSpecProfile.qOne
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · simp only [BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _
      (BinaryNestedSpecProfile.longInput_canonical input hC),padWithTrace_erasure]
  · split
    · simp only [BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _
        (BinaryNestedSpecProfile.shortInput_canonical input hC),padWithTrace_erasure]
    · rfl

def envelope (s : ℕ) : ℕ :=
  2 * BinaryThreeGeometryLifetime.comparisonEnvelope (2 * s + 1) +
    BinaryUnorderedThreeLifetime.envelope s + 4096 + 128

theorem boundaryWithTrace_usage (input : BinaryNestedParameters.Input)
    (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (boundaryWithTrace input).2 ≤ envelope s := by
  let zero := BinaryQuadraticExpressionLifetime.compareWithTrace input.q BinaryRationalOpcode.zero
  let one := BinaryQuadraticExpressionLifetime.compareWithTrace
    BinaryExpressionCompiler.Constant.one.word input.q
  have hQ : width input.q ≤ 2 * s + 1 := by
    have h := hC.2.2.2.2.2.2.trans (rationalWordWidth_of_height hH.2.2.2.2.2)
    omega
  have hZeroWidth : width BinaryRationalOpcode.zero ≤ 2 * s + 1 := by
    have h := (show CanonicalWord BinaryRationalOpcode.zero from ⟨BinaryRationalOpcode.zero_valid,by decide⟩).2.trans
      (rationalWordWidth_of_height (BinaryFactoryHeight.zero_height s hs))
    omega
  have hOneWidth : width BinaryExpressionCompiler.Constant.one.word ≤ 2 * s + 1 := by
    have h := (BinaryExpressionCompiler.Constant.word_canonical .one).2.trans
      (rationalWordWidth_of_height (BinaryFactoryHeight.one_height s hs))
    omega
  have hZero := BinaryThreeGeometryLifetime.comparison_usage input.q BinaryRationalOpcode.zero
    (2*s+1) hQ hZeroWidth
  have hOne := BinaryThreeGeometryLifetime.comparison_usage BinaryExpressionCompiler.Constant.one.word
    input.q (2*s+1) hOneWidth hQ
  have hLong := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage
    (BinaryNestedSpecProfile.longInput input) (BinaryNestedSpecProfile.longInput_canonical input hC)
    s hs (BinaryNestedSpecFactoryWork.longInput_height input s hs hH)
  have hShort := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage
    (BinaryNestedSpecProfile.shortInput input) (BinaryNestedSpecProfile.shortInput_canonical input hC)
    s hs (BinaryNestedSpecFactoryWork.shortInput_height input s hs hH)
  unfold boundaryWithTrace
  dsimp only
  split
  · have hPad := padWithTrace_usage
      (BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.longInput input)).1
    have hw := wrap_usage 32 2
      [zero.2,(BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.longInput input)).2,
        (padWithTrace (BinaryUnorderedThreeLifetime.descriptorWithTrace
          (BinaryNestedSpecProfile.longInput input)).1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [zero.2,
      (BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.longInput input)).2,
      (padWithTrace (BinaryUnorderedThreeLifetime.descriptorWithTrace
        (BinaryNestedSpecProfile.longInput input)).1).2]) ≤ _
    change usage zero.2 ≤ _ at hZero
    unfold envelope
    omega
  · split
    · have hPad := padWithTrace_usage
        (BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.shortInput input)).1
      have hw := wrap_usage 32 2
        [zero.2,one.2,(BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.shortInput input)).2,
          (padWithTrace (BinaryUnorderedThreeLifetime.descriptorWithTrace
            (BinaryNestedSpecProfile.shortInput input)).1).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2 [zero.2,one.2,
        (BinaryUnorderedThreeLifetime.descriptorWithTrace (BinaryNestedSpecProfile.shortInput input)).2,
        (padWithTrace (BinaryUnorderedThreeLifetime.descriptorWithTrace
          (BinaryNestedSpecProfile.shortInput input)).1).2]) ≤ _
      change usage zero.2 ≤ _ at hZero
      change usage one.2 ≤ _ at hOne
      unfold envelope
      omega
    · have hw := wrap_usage 32 2 [zero.2,one.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2 [zero.2,one.2]) ≤ _
      change usage zero.2 ≤ _ at hZero
      change usage one.2 ≤ _ at hOne
      unfold envelope
      omega

theorem all_prefix (input : BinaryNestedParameters.Input)
    (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (boundaryWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((boundaryWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (boundaryWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinaryNestedBoundaryLifetime
