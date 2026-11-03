import Blotto.BinaryReflectedNestedControlMeasured
import Blotto.BinaryCachedReflectedPrefixMeasured
import Blotto.BinaryNestedFirstProfileMeasured

/-! Original fields and seed parameters bound the measured reflected nested
control prefix, including reached boundary factories. Accepted physical-cache
fields instantiate it. A separate source-height/scalar-width polynomial covers
the complete first interior profile. Later regimes and model joins remain. -/
namespace Blotto.BinaryNestedControlMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial BinaryCachedFourBranchWork BinaryCachedFourParameterWork
open BinaryCachedThreeDescriptorWork BinaryCachedGroupInputHeight BinaryGroupInputs
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def jointEnvelope (s i cap : ℕ) : ℕ :=
  BinaryReflectedNestedControlMeasured.workEnvelope s i cap+BinaryReflectedNestedControlMeasured.envelope s i cap

theorem work_le_joint (s i cap : ℕ) :
    BinaryReflectedNestedControlMeasured.workEnvelope s i cap ≤ jointEnvelope s i cap := by unfold jointEnvelope; omega

theorem usage_le_joint (s i cap : ℕ) :
    BinaryReflectedNestedControlMeasured.envelope s i cap ≤ jointEnvelope s i cap := by unfold jointEnvelope; omega

macro "unfold_measured_nested_control" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryReflectedNestedControlMeasured.workEnvelope,BinaryReflectedNestedControlMeasured.envelope,
    BinaryNestedControlMeasured.workEnvelope,BinaryNestedControlMeasured.envelope,
    BinaryNestedControlMeasured.classifyPrice,BinaryNestedControlMeasured.classifyEnvelope,
    BinaryNestedControlMeasured.interiorPrice,BinaryNestedControlMeasured.interiorEnvelope,
    BinaryNestedBoundaryMeasured.workEnvelope,BinaryNestedBoundaryMeasured.envelope,
    BinaryNestedBoundaryMeasured.childPrice,BinaryNestedBoundaryMeasured.childEnvelope,
    BinaryNestedOrderMeasured.workEnvelope,BinaryNestedOrderLifetime.orderEnvelope,
    BinaryNestedParameterMeasured.workEnvelope,BinaryNestedParameterMeasured.envelope,
    BinaryNestedParameterMeasured.expressionWork,BinaryNestedParameterMeasured.expressionCells,BinaryNestedParameterMeasured.expressionFrames,
    BinaryNestedRegimeMeasured.workEnvelope,BinaryNestedRegimeMeasured.widthEnvelope,BinaryNestedRegimeLifetime.envelope,
    BinarySmallUniformSplitMeasured.opcodePrice,BinaryThreeGeometryLifetime.comparisonEnvelope,BinaryLifetimeUsage.opcodeEnvelope]
  <;> unfold_measured_group_factory
  <;> unfold_measured_reflected_prefix)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_nested_control
  resource_polynomial

theorem joint_mono {s i cap t I B : ℕ} (hs : s ≤ t) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s i cap ≤ jointEnvelope t I B := by
  unfold_measured_nested_control
  unfold expressionHeightBudget
  gcongr <;> (apply binaryWordWidth_mono; gcongr)

theorem joint_polynomial : ∃ C d : ℕ,∀ s i cap,jointEnvelope s i cap ≤ C*(s+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s i cap
  let T := s+i+cap
  have hm : jointEnvelope s i cap ≤ jointEnvelope T T T := joint_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryReflectedNestedControlMeasured.run store input hC pc hp).2 ≤ C*(s+store.width+store.cap.value+2)^d ∧
      usage (BinaryReflectedNestedControlMeasured.run store input hC pc hp).1.2 ≤ C*(s+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp
  have h := BinaryReflectedNestedControlMeasured.run_bounds store input source hC hR hCase s hs hH pc hp
  have hb := hBound s store.width store.cap.value
  exact ⟨h.1.trans ((work_le_joint _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryReflectedNestedControlMeasured.run store input hC pc hp).1.2 steps ≤ borrowed+C*(s+store.width+store.cap.value+2)^d ∧
      framePeak ((BinaryReflectedNestedControlMeasured.run store input hC pc hp).1.2.take steps) ≤ C*(s+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase s hs hH pc hp).2 borrowed steps

def checkedRun (checked : Checked) (store : BinarySeedLookupTree.Store)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :=
  BinaryReflectedNestedControlMeasured.run store checked.ordered checked.ordered_canonical pc hp

theorem checked_bounds (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (checkedRun checked store pc hp).2 ≤ jointEnvelope s store.width store.cap.value ∧
      usage (checkedRun checked store pc hp).1.2 ≤ jointEnvelope s store.width store.cap.value := by
  obtain ⟨source,hR⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
  have hCase : source.fourInput.input.w < (1-source.fourInput.input.p)*source.fourInput.input.ell :=
    lt_of_not_ge (fun h => hGuard ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
      checked.ordered_canonical hRef).mpr h))
  have h := BinaryReflectedNestedControlMeasured.run_bounds store checked.ordered source.fourInput.input
    checked.ordered_canonical hRef hCase s hs (source_four_heights checked.input source hR s hH).input pc hp
  exact ⟨h.1.trans (work_le_joint _ _ _),h.2.trans (usage_le_joint _ _ _)⟩

theorem accepted_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (i cap : ℕ),
    jointEnvelope (inputHeight parsed.1.2.logical.request) i cap ≤ C*(frame.length+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed i cap
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+i+cap+2 ≤ 34*(frame.length+i+cap+2) := by unfold inputHeight; omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) i cap).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
      (fromCached store parsed.1.2.logical.request rich result
        (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot).ordered = true)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (checkedRun checked store pc hp).2 ≤ C*(frame.length+store.width+store.cap.value+2)^d ∧
      usage (checkedRun checked store pc hp).1.2 ≤ C*(frame.length+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot hGuard pc hp
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound
  let checked := fromCached store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hHeight := fromCached_height store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hs : 2 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := checked_bounds checked hGuard _ hs hHeight store pc hp
  have hb := hBound frame parsed hParsed store.width store.cap.value
  have hResult : (checkedRun checked store pc hp).2 ≤ C*(frame.length+store.width+store.cap.value+2)^d ∧
      usage (checkedRun checked store pc hp).1.2 ≤ C*(frame.length+store.width+store.cap.value+2)^d := ⟨h.1.trans hb,h.2.trans hb⟩
  with_reducible exact hResult

def firstEnvelope (s K : ℕ) : ℕ :=
  BinaryNestedFirstProfileMeasured.workEnvelope s K+BinaryNestedFirstProfileMeasured.envelope s K

theorem first_work_le (s K : ℕ) :
    BinaryNestedFirstProfileMeasured.workEnvelope s K ≤ firstEnvelope s K := by unfold firstEnvelope; omega

theorem first_usage_le (s K : ℕ) :
    BinaryNestedFirstProfileMeasured.envelope s K ≤ firstEnvelope s K := by unfold firstEnvelope; omega

macro "unfold_measured_nested_first" : tactic => `(tactic|
  simp only [firstEnvelope,BinaryNestedFirstProfileMeasured.workEnvelope,BinaryNestedFirstProfileMeasured.envelope,
    BinaryNestedFirstLocationMeasured.workEnvelope,BinaryNestedFirstLocationMeasured.envelope,
    BinaryNestedFirstDescriptorMeasured.workEnvelope,BinaryNestedFirstDescriptorMeasured.envelope,
    BinaryNestedFirstDescriptorMeasured.positivePrice,BinaryNestedFirstDescriptorMeasured.positiveEnvelope,
    BinaryNestedFirstDescriptorMeasured.shiftWidth,
    BinaryNestedFirstAssemblyMeasured.shiftPrice,BinaryNestedFirstAssemblyMeasured.shiftEnvelope,
    BinaryNestedFirstAssemblyMeasured.rowsPrice,BinaryNestedFirstAssemblyMeasured.rowsEnvelope,
    BinaryNestedFirstAssemblyMeasured.rowPrice,BinaryNestedFirstAssemblyMeasured.rowEnvelope,
    BinaryReflectedSystemMeasured.opcodePrice,
    BinaryNestedParameterMeasured.workEnvelope,BinaryNestedParameterMeasured.envelope,
    BinaryNestedParameterMeasured.expressionWork,BinaryNestedParameterMeasured.expressionCells,BinaryNestedParameterMeasured.expressionFrames,
    BinaryThreeGeometryLifetime.comparisonEnvelope,BinaryLifetimeUsage.opcodeEnvelope]
  <;> unfold_measured_group_factory)

theorem first_diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => firstEnvelope p.wordWidth p.wordWidth) := by
  unfold_measured_nested_first
  resource_polynomial

theorem first_mono {s K t N : ℕ} (hs : s ≤ t) (hK : K ≤ N) : firstEnvelope s K ≤ firstEnvelope t N := by
  unfold_measured_nested_first
  unfold expressionHeightBudget
  gcongr

theorem first_polynomial : ∃ C d : ℕ,∀ s K,firstEnvelope s K ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := first_diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s K
  let T := s+K
  have hm : firstEnvelope s K ≤ firstEnvelope T T := first_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem first_source_bounds : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (hC : input.Canonical)
    (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K),
    (BinaryNestedFirstProfileMeasured.profile input K bits).2 ≤ C*(s+K+2)^d ∧
      usage (BinaryNestedFirstProfileMeasured.profile input K bits).1.2 ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := first_polynomial
  refine ⟨C,d,?_⟩
  intro input hC s hs hH K bits
  have h := BinaryNestedFirstProfileMeasured.profile_bounds input hC s hs hH K bits
  have hb := hBound s K
  exact ⟨h.1.trans ((first_work_le _ _).trans hb),h.2.trans ((first_usage_le _ _).trans hb)⟩

theorem first_source_all_prefix : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (hC : input.Canonical)
    (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryNestedFirstProfileMeasured.profile input K bits).1.2 steps ≤ borrowed+C*(s+K+2)^d ∧
      framePeak ((BinaryNestedFirstProfileMeasured.profile input K bits).1.2.take steps) ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := first_source_bounds
  refine ⟨C,d,?_⟩
  intro input hC s hs hH K bits borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound input hC s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedControlMeasuredPolynomial
