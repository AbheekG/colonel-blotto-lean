import Blotto.BinaryNestedFirstAssemblyLifetime

/-! Complete first-regime conditional descriptor at an already constructed
location: one parameter table, positivity guard, regular geometry and shifted
three-variable table, or the explicit zero-probability corner. -/
namespace Blotto.BinaryNestedFirstDescriptorLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def descriptorWithTrace (input : Input) (x : SignedWord) : Segment × Trace :=
  let parameters := BinaryNestedParameterAtLifetime.prepareWithTrace input x
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace
    (parameters.1.read 4) BinaryRationalOpcode.zero
  if !guard.1 then
    let geometry := BinaryNestedParameterAtLifetime.geometryWithTrace input x
    let table := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace geometry.1
    let shifted := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace table.1 x
    (shifted.1,wrap 40 3 [parameters.2,guard.2,geometry.2,table.2,shifted.2])
  else
    let corner := BinaryNestedFirstAssemblyLifetime.cornerWithTrace input x
    (corner.1,wrap 40 3 [parameters.2,guard.2,corner.2])

theorem descriptorWithTrace_erasure (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x) :
    (descriptorWithTrace input x).1 = BinaryNestedFirstConditional.descriptor input x := by
  have hParameters := BinaryNestedParameterAtLifetime.prepareWithTrace_erasure input x hC hX
  have hGeometry := BinaryNestedParameterAtLifetime.geometryWithTrace_erasure input x hC hX
  have hGeometryC := BinaryNestedParameters.geometry_canonical input x hC hX
  have hTable := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases
    (BinaryNestedParameterAtLifetime.geometryWithTrace input x).1
    (by rw [hGeometry]; exact hGeometryC)
  have hTableC : (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace
      (BinaryNestedParameterAtLifetime.geometryWithTrace input x).1).1.Canonical := by
    rw [hTable,hGeometry]
    exact BinaryThreeDescriptorCompiler.descriptor_canonical _ hGeometryC
  have hShift := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace_erasure
    (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace
      (BinaryNestedParameterAtLifetime.geometryWithTrace input x).1).1 x hTableC hX
  unfold descriptorWithTrace BinaryNestedFirstConditional.descriptor
  dsimp only
  rw [hParameters]
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · rw [← hGeometry,hShift,hTable]
  · exact BinaryNestedFirstAssemblyLifetime.cornerWithTrace_erasure input x

def envelope (s : ℕ) : ℕ :=
  let H := expressionHeightBudget s 16
  let T := expressionHeightBudget H 16
  BinaryNestedParameterLifetime.envelope s +
    BinaryThreeGeometryLifetime.comparisonEnvelope (2 * H + 1) +
    BinaryNestedParameterAtLifetime.geometryEnvelope s +
    BinaryQuadraticThreeFactoryLifetime.bound H + BinaryQuadraticThreeFactoryLifetime.frames H +
    BinaryNestedFirstAssemblyLifetime.shiftEnvelope (2 * T + 1) + 4096 + 192

theorem descriptorWithTrace_usage (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hXH : RationalHeight (value x) s) :
    usage (descriptorWithTrace input x).2 ≤ envelope s := by
  let H := expressionHeightBudget s 16
  let T := expressionHeightBudget H 16
  let parameters := BinaryNestedParameterAtLifetime.prepareWithTrace input x
  let geometry := BinaryNestedParameterAtLifetime.geometryWithTrace input x
  let table := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace geometry.1
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace
    (parameters.1.read 4) BinaryRationalOpcode.zero
  have hParameters := BinaryNestedParameterAtLifetime.prepareWithTrace_usage input x hC hX s hs hH hXH
  change usage parameters.2 ≤ _ at hParameters
  have hParametersState := BinaryNestedParameterAtLifetime.prepareWithTrace_erasure input x hC hX
  have hP4 : width (parameters.1.read 4) ≤ 2 * H + 1 := by
    rw [hParametersState]
    have h := (BinaryNestedParameters.prepare_canonical input x hC hX 4).2.trans
      (rationalWordWidth_of_height
        (BinaryNestedParameterWork.prepare_height input x hC hX s hs hH hXH 4))
    change width ((BinaryNestedParameters.prepare input x).read 4) ≤ 2 * H + 1
    dsimp only [H]
    omega
  have hZero : width BinaryRationalOpcode.zero ≤ 2 * H + 1 := by
    have h := (show CanonicalWord BinaryRationalOpcode.zero from
      ⟨BinaryRationalOpcode.zero_valid,by decide⟩).2.trans
      (rationalWordWidth_of_height (BinaryFactoryHeight.zero_height s hs))
    have hm := expressionHeightBudget_ge_input s 16
    dsimp only [H]
    omega
  have hGuard := BinaryThreeGeometryLifetime.comparison_usage
    (parameters.1.read 4) BinaryRationalOpcode.zero (2*H+1) hP4 hZero
  change usage guard.2 ≤ _ at hGuard
  have hGeometry := BinaryNestedParameterAtLifetime.geometryWithTrace_usage input x
    hC hX s hs hH hXH
  change usage geometry.2 ≤ _ at hGeometry
  have hGeometryState := BinaryNestedParameterAtLifetime.geometryWithTrace_erasure input x hC hX
  have hGeometryC : ∀ j, CanonicalWord (geometry.1.read j) := by
    rw [hGeometryState]
    exact BinaryNestedParameters.geometry_canonical input x hC hX
  have hGeometryH : BinarySyntaxUniformWork.EnvHeight geometry.1 H := by
    intro j
    rw [hGeometryState]
    exact BinaryNestedParameterWork.geometry_height input x hC hX s hs hH hXH j
  have hTableBounds := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_bounds
    geometry.1 hGeometryC H (hs.trans (expressionHeightBudget_ge_input s 16)) hGeometryH
  have hTableUsage : usage table.2 ≤
      BinaryQuadraticThreeFactoryLifetime.bound H + BinaryQuadraticThreeFactoryLifetime.frames H := by
    change listCells table.2 + arraySlots table.2 ≤ _ ∧ framePeak table.2 ≤ _ at hTableBounds
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hTableState := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases geometry.1 hGeometryC
  have hTableC : table.1.Canonical := by
    rw [hTableState]
    exact BinaryThreeDescriptorCompiler.descriptor_canonical _ hGeometryC
  have hTableH : BinaryFactoryHeight.SegmentHeight table.1 T := by
    rw [hTableState]
    exact BinaryThreeFactoryWork.descriptor_height geometry.1 hGeometryC H
      (hs.trans (expressionHeightBudget_ge_input s 16)) hGeometryH
  have hXW : width x ≤ 2 * T + 1 := by
    have h := hX.2.trans (rationalWordWidth_of_height hXH)
    have hm := (expressionHeightBudget_ge_input s 16).trans
      (expressionHeightBudget_ge_input H 16)
    dsimp only [H,T] at hm ⊢
    omega
  have hP : ∀ slot,width ((table.1.P.read slot).read 2) ≤ 2 * T + 1 := by
    intro slot
    have h := (hTableC.2.1 slot 2).2.trans
      (rationalWordWidth_of_height (hTableH.2 slot 2).1)
    dsimp only [T]
    omega
  have hQ : ∀ slot,width ((table.1.Q.read slot).read 2) ≤ 2 * T + 1 := by
    intro slot
    have h := (hTableC.2.2 slot 2).2.trans
      (rationalWordWidth_of_height (hTableH.2 slot 2).2)
    dsimp only [T]
    omega
  have hShift := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace_usage table.1 x
    (2*T+1) hP hQ hXW
  have hCorner := BinaryNestedFirstAssemblyLifetime.cornerWithTrace_usage input x
  unfold descriptorWithTrace
  dsimp only
  split
  · have hw := wrap_usage 40 3 [parameters.2,guard.2,geometry.2,table.2,
      (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace table.1 x).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [parameters.2,guard.2,geometry.2,table.2,
      (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace table.1 x).2]) ≤ _
    unfold envelope
    dsimp only [H,T] at *
    omega
  · have hw := wrap_usage 40 3 [parameters.2,guard.2,
      (BinaryNestedFirstAssemblyLifetime.cornerWithTrace input x).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [parameters.2,guard.2,
      (BinaryNestedFirstAssemblyLifetime.cornerWithTrace input x).2]) ≤ _
    unfold envelope
    dsimp only [H,T] at *
    omega

theorem all_prefix (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hXH : RationalHeight (value x) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace input x).2 steps ≤ borrowed + envelope s ∧
    framePeak ((descriptorWithTrace input x).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (descriptorWithTrace_usage input x hC hX s hs hH hXH) borrowed steps

end Blotto.BinaryNestedFirstDescriptorLifetime
