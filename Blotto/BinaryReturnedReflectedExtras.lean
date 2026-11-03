import Blotto.BinaryReturnedCategoricalExtras
import Blotto.BinaryReflectedLowerSampleMeasured
import Blotto.BinaryCachedReflectedDrawMeasured

/-! Returned normalization extras through actual reflected point/subtraction,
selection, lower fallback and cached draw interfaces. Factories/resource work,
metadata evaluation and full native/physical costs remain separate. -/
namespace Blotto.BinaryReturnedReflectedExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup BinaryCachedFourBranchWork
open BinaryCachedThreeDescriptorWork BinaryGroupInputs BinaryGroupSamplers
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached)
open BinaryReflectedDrawMeasured (Reached)
open BinaryReflectedEmissionMeasured (Segment)
set_option autoImplicit false
set_option maxHeartbeats 3500000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem reflect_extra (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    (BinaryReflectedEmissionMeasured.reflectWithExtras input row).2 =
      ∑ j : Fin 3, BinaryPlannedQuadratic.extra .sub ((originalLengths input).read j) (row.read j) := by
  simp only [BinaryReflectedEmissionMeasured.reflectWithExtras,BinaryLifetimeArrayExtras.build_extra,
    BinaryNormalizedCoordinate.opcode_extra]

theorem reflect_bound (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    (BinaryReflectedEmissionMeasured.reflectWithExtras input row).2 ≤
      155*(BinaryReflectedEmissionMeasured.reflectWithExtras input row).1.2 := by
  have h := BinaryLifetimeArrayExtras.build_bound 3 (fun j =>
    BinaryNormalizedCoordinate.opcode .sub ((originalLengths input).read j) (row.read j)) 155
    (fun j => BinaryNormalizationExtraWork.opcode_bound .sub ((originalLengths input).read j) (row.read j))
  dsimp only [BinaryReflectedEmissionMeasured.reflectWithExtras,BinaryReflectedEmissionMeasured.collectRow]
  omega

theorem sample_bound (input : BinaryFourParameters.Input) (table : BinaryReflectedEmissionMeasured.Segment)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (BinaryReflectedEmissionMeasured.sampleWithExtras input table slot K scalar).2 ≤
      155*(BinaryReflectedEmissionMeasured.sampleWithExtras input table slot K scalar).1.2 := by
  have hp := BinaryReturnedInterpolationExtras.sample_bound table slot K scalar
  have hr := reflect_bound input (BinaryPhysicalPointMeasured.sampleWithExtras table slot K scalar).1.1.1
  dsimp only [BinaryReflectedEmissionMeasured.sampleWithExtras,BinaryReflectedEmissionMeasured.collect]
  omega

theorem table_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryReflectedTableDrawMeasured.runWithExtras store input prepared K scalar pc hp).2 ≤
      155*(BinaryReflectedTableDrawMeasured.runWithExtras store input prepared K scalar pc hp).1.2 := by
  have hs := BinaryReturnedCategoricalExtras.select_bound store prepared (0 : Fin 18) pc hp
  dsimp only [BinaryReflectedTableDrawMeasured.runWithExtras]
  cases h : (BinaryWordSegmentMeasured.selectWithExtras store prepared (0 : Fin 18) pc hp).1.1.1.1 with
  | none => dsimp only; omega
  | some slot =>
      dsimp only
      have he := sample_bound input prepared.table slot K scalar
      omega

theorem lower_bound (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras input hC hAd K outer scalar).2 ≤
      155*(BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras input hC hAd K outer scalar).1.2 := by
  let prepared := BinaryReflectedLowerFactoryMeasured.prepared input hC hAd K outer
  have hs := BinaryReturnedCategoricalExtras.lower_segment_bound prepared.1.1 0
  have he := sample_bound input prepared.1.1.table
    (BinaryCategoricalLowerMeasured.segmentWithExtras prepared.1.1 0).1.1.1 K scalar
  dsimp only [BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras,BinaryReflectedLowerSampleMeasured.collect]
  change (BinaryCategoricalLowerMeasured.segmentWithExtras prepared.1.1 0).2+
      (BinaryReflectedEmissionMeasured.sampleWithExtras input prepared.1.1.table
        (BinaryCategoricalLowerMeasured.segmentWithExtras prepared.1.1 0).1.1.1 K scalar).2 ≤ _
  dsimp only [prepared] at hs he ⊢
  omega

theorem after_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryReflectedDrawMeasured.afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤
      155*(BinaryReflectedDrawMeasured.afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.2 := by
  simp only [BinaryReflectedDrawMeasured.afterResourceWithDrawExtras_record]
  split
  · change (0 : ℕ) ≤155*4
    omega
  · rename_i result hResult
    dsimp only
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
    let terminal := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
      (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
    have ht := table_bound store input terminal.1.1 K scalar resource.2
      (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
    dsimp only [terminal] at ht
    omega

theorem reached_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : BinaryReflectedDrawMeasured.Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (BinaryReflectedDrawMeasured.fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤
      155*(BinaryReflectedDrawMeasured.fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).1.2 := by
  have h := after_bound store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  simp only [BinaryReflectedDrawMeasured.fromReachedWithDrawExtras_record,BinaryReflectedDrawMeasured.join]
  omega

theorem run_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryReflectedDrawMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      155*(BinaryReflectedDrawMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryReflectedDrawMeasured.runWithDrawExtras_record]
  exact reached_bound store input hC hAd K outer scalar pc hp _ (BinaryReflectedResourceMeasured.run_resource store input hC pc hp)

theorem cached_bound (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).2 ≤
      155*(BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.2 := by
  exact run_bound store checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard) K outer scalar pc hp

theorem reflect_price (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) (W : ℕ)
    (hLengths : ∀ j,width ((originalLengths input).read j) ≤ W) (hRow : ∀ j,width (row.read j) ≤ W) :
    (BinaryReflectedEmissionMeasured.reflectWithExtras input row).1.2+(BinaryReflectedEmissionMeasured.reflectWithExtras input row).2 ≤
      156*(BinaryReflectedEmissionMeasured.reflectPrice W) := by
  have he := reflect_bound input row
  have hw := (BinaryReflectedEmissionMeasured.reflect_bounds input row W hLengths hRow).1
  simp only [BinaryReflectedEmissionMeasured.reflectWithExtras_compat] at he ⊢
  omega

theorem sample_price (input : BinaryFourParameters.Input) (hC : input.Canonical) (table : Segment) (hTable : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s)
    (hEndpoint : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧ RationalHeight (value ((table.Q.read slot).read j)) s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (BinaryReflectedEmissionMeasured.sampleWithExtras input table slot K scalar).1.2+(BinaryReflectedEmissionMeasured.sampleWithExtras input table slot K scalar).2 ≤
      156*(BinaryReflectedEmissionMeasured.workEnvelope s K) := by
  have he := sample_bound input table slot K scalar
  have hw := (BinaryReflectedEmissionMeasured.sample_bounds input hC table hTable s hs hEndpoint hLengths slot K scalar).1
  simp only [BinaryReflectedEmissionMeasured.sampleWithExtras_compat] at he ⊢
  omega

theorem table_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (source : RationalSegmentLottery 3 18) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((BinaryReflectedFourSetup.originalLengths input).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryReflectedTableDrawMeasured.runWithExtras store input prepared K scalar pc hp).1.2+(BinaryReflectedTableDrawMeasured.runWithExtras store input prepared K scalar pc hp).2 ≤
      156*(BinaryReflectedTableDrawMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := table_bound store input prepared K scalar pc hp
  have hw := (BinaryReflectedTableDrawMeasured.run_bounds store input hC prepared source hR s hs hHeight hLengths K scalar pc hp).1
  simp only [BinaryReflectedTableDrawMeasured.runWithExtras_compat] at he ⊢
  omega

theorem lower_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras input hC hAd K outer scalar).1.2+(BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras input hC hAd K outer scalar).2 ≤
      156*(BinaryReflectedLowerSampleMeasured.workEnvelope s K) := by
  have he := lower_bound input hC hAd K outer scalar
  have hw := (BinaryReflectedLowerSampleMeasured.sample_bounds input source hC hR hCase hAd s hs hH K outer scalar).1
  simp only [BinaryReflectedLowerSampleMeasured.sampleWithDrawExtras_compat] at he ⊢
  omega

theorem after_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryReflectedDrawMeasured.afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.2+(BinaryReflectedDrawMeasured.afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤
      156*(BinaryReflectedDrawMeasured.afterPrice s K store.width store.cap.value) := by
  have he := after_bound store input hC hAd cached pc hp resource hResource K outer scalar
  have hw := (BinaryReflectedDrawMeasured.afterResource_bounds store input source hC hR hCase hAd s hs hH cached pc hp resource hResource K outer scalar).1
  simp only [BinaryReflectedDrawMeasured.afterResourceWithDrawExtras_compat] at he ⊢
  omega

theorem reached_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (hReached : reached.2 ≤ BinaryReflectedResourceMeasured.workEnvelope s store.width store.cap.value ∧
      usage reached.1.2 ≤ BinaryReflectedResourceMeasured.envelope s store.width store.cap.value) :
    (BinaryReflectedDrawMeasured.fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).1.2+(BinaryReflectedDrawMeasured.fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤
      156*(BinaryReflectedDrawMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := reached_bound store input hC hAd K outer scalar pc hp reached hResource
  have hw := (BinaryReflectedDrawMeasured.fromReached_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp reached hResource hReached).1
  simp only [BinaryReflectedDrawMeasured.fromReachedWithDrawExtras_compat] at he ⊢
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryReflectedDrawMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryReflectedDrawMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      156*(BinaryReflectedDrawMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := run_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryReflectedDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryReflectedDrawMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem cached_price (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.2+(BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).2 ≤
      156*(BinaryReflectedDrawMeasuredPolynomial.jointEnvelope s K store.width store.cap.value) := by
  have he := cached_bound checked hGuard store K outer scalar pc hp
  have hw := (BinaryCachedReflectedDrawMeasured.run_bounds checked hGuard s hs hH store K outer scalar pc hp).1
  simp only [BinaryCachedReflectedDrawMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem accepted_cached_price : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
      (fromCached store parsed.1.2.logical.request rich result
        (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot).ordered = true)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.2+(BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.1.2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryCachedReflectedDrawMeasured.accepted_cached_bounds
  refine ⟨156*C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot hGuard K outer scalar pc hp
  let checked := fromCached store parsed.1.2.logical.request rich result
    (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
  have hw := hOld frame parsed hParsed store rich result hFound hCount selected hPivot hGuard K outer scalar pc hp
  have he := cached_bound checked hGuard store K outer scalar pc hp
  change (BinaryCachedReflectedDrawMeasured.run checked hGuard store K outer scalar pc hp).2 ≤
      C*(frame.length+K+store.width+store.cap.value+2)^d ∧
    usage (BinaryCachedReflectedDrawMeasured.run checked hGuard store K outer scalar pc hp).1.2 ≤
      C*(frame.length+K+store.width+store.cap.value+2)^d at hw
  change (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.2+(BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).2 ≤ (156*C)*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryCachedReflectedDrawMeasured.runWithDrawExtras checked hGuard store K outer scalar pc hp).1.1.2 ≤ (156*C)*(frame.length+K+store.width+store.cap.value+2)^d
  simp only [BinaryCachedReflectedDrawMeasured.runWithDrawExtras_compat,Nat.mul_assoc] at he ⊢
  constructor <;> omega

end Blotto.BinaryReturnedReflectedExtras
