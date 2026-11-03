import Blotto.BinaryReflectedProfilePrefixMeasured
import Blotto.BinaryNestedProfileMeasuredPolynomial
import Blotto.BinaryCachedReflectedPrefixMeasured

/-! Original fields, scalar width and seed parameters bound the complete
measured reflected profile prefix through all boundary/interior factories and
coordinate restoration. Accepted physical-cache fields instantiate the bounds.
Selection/interpolation/emission and complete native model joins remain. -/
namespace Blotto.BinaryReflectedProfileMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial BinaryCachedFourBranchWork BinaryCachedFourParameterWork
open BinaryCachedThreeDescriptorWork BinaryCachedGroupInputHeight BinaryGroupInputs
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def jointEnvelope (s i cap K : ℕ) : ℕ :=
  BinaryReflectedProfilePrefixMeasured.workEnvelope s i cap K+BinaryReflectedProfilePrefixMeasured.envelope s i cap K

theorem work_le_joint (s i cap K : ℕ) :
    BinaryReflectedProfilePrefixMeasured.workEnvelope s i cap K ≤ jointEnvelope s i cap K := by unfold jointEnvelope; omega

theorem usage_le_joint (s i cap K : ℕ) :
    BinaryReflectedProfilePrefixMeasured.envelope s i cap K ≤ jointEnvelope s i cap K := by unfold jointEnvelope; omega

macro "unfold_measured_reflected_profile" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryReflectedProfilePrefixMeasured.workEnvelope,BinaryReflectedProfilePrefixMeasured.envelope]
  <;> unfold_measured_nested_profile
  <;> unfold_measured_reflected_prefix)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  obtain ⟨C,d,hNested⟩ := BinaryNestedProfileMeasuredPolynomial.joint_polynomial
  have hGrowth : NaturalPolynomialEnvelope inputSize (fun p => expressionHeightBudget p.wordWidth 23+p.wordWidth+2) := by
    resource_polynomial
  have hActual : NaturalPolynomialEnvelope inputSize (fun p =>
      BinaryNestedProfileMeasuredPolynomial.jointEnvelope (expressionHeightBudget p.wordWidth 23) p.wordWidth) :=
    NaturalPolynomialEnvelope.dominated
      (NaturalPolynomialEnvelope.mul (NaturalPolynomialEnvelope.constant inputSize C)
        (NaturalPolynomialEnvelope.pow hGrowth d)) (fun p => hNested _ _)
  have hSum := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add BinaryReflectedPrefixMeasuredPolynomial.diagonal_polynomial hActual)
    (NaturalPolynomialEnvelope.constant inputSize 48)
  apply NaturalPolynomialEnvelope.dominated hSum
  intro p
  simp only [jointEnvelope,BinaryReflectedProfilePrefixMeasured.workEnvelope,BinaryReflectedProfilePrefixMeasured.envelope,
    BinaryReflectedPrefixMeasuredPolynomial.jointEnvelope,BinaryNestedProfileMeasuredPolynomial.jointEnvelope]
  omega

theorem joint_mono {s i cap K t I B N : ℕ} (hs : s ≤ t) (hi : i ≤ I) (hb : cap ≤ B) (hk : K ≤ N) :
    jointEnvelope s i cap K ≤ jointEnvelope t I B N := by
  unfold_measured_reflected_profile
  unfold expressionHeightBudget
  gcongr <;> (apply binaryWordWidth_mono; gcongr)

theorem joint_polynomial : ∃ C d : ℕ,∀ s i cap K,jointEnvelope s i cap K ≤ C*(s+i+cap+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s i cap K
  let T := s+i+cap+K
  have hm : jointEnvelope s i cap K ≤ jointEnvelope T T T T := joint_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (K : ℕ) (bits : BinaryScalarTape K),
    (BinaryReflectedProfilePrefixMeasured.run store input hC pc hp K bits).2 ≤ C*(s+store.width+store.cap.value+K+2)^d ∧
      usage (BinaryReflectedProfilePrefixMeasured.run store input hC pc hp K bits).1.2 ≤ C*(s+store.width+store.cap.value+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp K bits
  have h := BinaryReflectedProfilePrefixMeasured.run_bounds store input source hC hR hCase s hs hH pc hp K bits
  have hb := hBound s store.width store.cap.value K
  exact ⟨h.1.trans ((work_le_joint _ _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryReflectedProfilePrefixMeasured.run store input hC pc hp K bits).1.2 steps ≤ borrowed+C*(s+store.width+store.cap.value+K+2)^d ∧
      framePeak ((BinaryReflectedProfilePrefixMeasured.run store input hC pc hp K bits).1.2.take steps) ≤ C*(s+store.width+store.cap.value+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp K bits borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase s hs hH pc hp K bits).2 borrowed steps

def checkedRun (checked : Checked) (store : BinarySeedLookupTree.Store)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (K : ℕ) (bits : BinaryScalarTape K) :=
  BinaryReflectedProfilePrefixMeasured.run store checked.ordered checked.ordered_canonical pc hp K bits

theorem checked_bounds (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (K : ℕ) (bits : BinaryScalarTape K) :
    (checkedRun checked store pc hp K bits).2 ≤ jointEnvelope s store.width store.cap.value K ∧
      usage (checkedRun checked store pc hp K bits).1.2 ≤ jointEnvelope s store.width store.cap.value K := by
  obtain ⟨source,hR⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
  have hCase : source.fourInput.input.w < (1-source.fourInput.input.p)*source.fourInput.input.ell :=
    lt_of_not_ge (fun h => hGuard ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
      checked.ordered_canonical hRef).mpr h))
  have h := BinaryReflectedProfilePrefixMeasured.run_bounds store checked.ordered source.fourInput.input
    checked.ordered_canonical hRef hCase s hs (source_four_heights checked.input source hR s hH).input pc hp K bits
  exact ⟨h.1.trans (work_le_joint _ _ _ _),h.2.trans (usage_le_joint _ _ _ _)⟩

theorem accepted_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (i cap K : ℕ),
    jointEnvelope (inputHeight parsed.1.2.logical.request) i cap K ≤ C*(frame.length+i+cap+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed i cap K
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+i+cap+K+2 ≤ 34*(frame.length+i+cap+K+2) := by unfold inputHeight; omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) i cap K).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
      (fromCached store parsed.1.2.logical.request rich result
        (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot).ordered = true)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (K : ℕ) (bits : BinaryScalarTape K),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (checkedRun checked store pc hp K bits).2 ≤ C*(frame.length+store.width+store.cap.value+K+2)^d ∧
      usage (checkedRun checked store pc hp K bits).1.2 ≤ C*(frame.length+store.width+store.cap.value+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot hGuard pc hp K bits
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound
  let checked := fromCached store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hHeight := fromCached_height store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hs : 2 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := checked_bounds checked hGuard _ hs hHeight store pc hp K bits
  have hb := hBound frame parsed hParsed store.width store.cap.value K
  have hResult : (checkedRun checked store pc hp K bits).2 ≤ C*(frame.length+store.width+store.cap.value+K+2)^d ∧
      usage (checkedRun checked store pc hp K bits).1.2 ≤ C*(frame.length+store.width+store.cap.value+K+2)^d := ⟨h.1.trans hb,h.2.trans hb⟩
  with_reducible exact hResult

end Blotto.BinaryReflectedProfileMeasuredPolynomial
