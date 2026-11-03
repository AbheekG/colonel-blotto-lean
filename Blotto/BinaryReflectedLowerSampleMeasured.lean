import Blotto.BinaryReflectedLowerFactoryMeasured
import Blotto.BinaryCategoricalLowerMeasured
import Blotto.BinaryReflectedEmissionMeasured
import Blotto.BinaryReflectedLowerSampleLifetime

/-! Complete measured deterministic reflected fallback: physical resource
completion, one terminal/profile table, deterministic lower categorical
selection, physical interpolation and reflection. The actual returned table
and selected slot flow into emission, with original-field source bounds and
the original canonical, box and full-budget output on every scalar tape. -/
namespace Blotto.BinaryReflectedLowerSampleMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 1500000

def collect (prepared : (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ)
    (selected : (Fin 18 × Trace) × ℕ) (emitted : (FixedArrayTable 4 SignedWord × Trace) × ℕ) :
    (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  ((emitted.1.1,wrap 40 3 [prepared.1.2,selected.1.2,emitted.1.2]),prepared.2+selected.2+emitted.2+12)

set_option cleanup.letToHave false in
def sampleWithDrawExtras (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  let prepared := BinaryReflectedLowerFactoryMeasured.prepared input hC hAd K outer
  let chosen := BinaryCategoricalLowerMeasured.segmentWithExtras prepared.1.1 0
  let selected := chosen.1
  let result := BinaryReflectedEmissionMeasured.sampleWithExtras input prepared.1.1.table selected.1.1 K scalar
  (collect prepared selected result.1,chosen.2+result.2)

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (sampleWithDrawExtras input hC hAd K outer scalar).1

theorem sampleWithDrawExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    (sampleWithDrawExtras input hC hAd K outer scalar).1 = sample input hC hAd K outer scalar := rfl

theorem sample_record (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    sample input hC hAd K outer scalar =
  let prepared := BinaryReflectedLowerFactoryMeasured.prepared input hC hAd K outer
  let selected := BinaryCategoricalLowerMeasured.segment prepared.1.1 0
  let emitted := BinaryReflectedEmissionMeasured.sample input prepared.1.1.table selected.1.1 K scalar
  collect prepared selected emitted := by
  simp only [sample,sampleWithDrawExtras,BinaryCategoricalLowerMeasured.segmentWithExtras_compat,
    BinaryReflectedEmissionMeasured.sampleWithExtras_compat]


theorem sample_data (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (sample input hC hAd K outer scalar).1.1 =
      (BinaryReflectedLowerSampleLifetime.sampleWithTrace input hC hAd K outer scalar).1 := by
  simp only [sample_record,collect,BinaryReflectedLowerSampleLifetime.sampleWithTrace,
    BinaryReflectedEmissionMeasured.sample_data,BinaryCategoricalLowerMeasured.segment_erases,
    BinaryReflectedLowerFactoryMeasured.prepared_data]

theorem sample_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (sample input hC hAd K outer scalar).1.1 = BinaryTerminalFallback.sample input hC hAd K outer scalar := by
  rw [sample_data]
  exact BinaryReflectedLowerSampleLifetime.sampleWithTrace_erasure input hC hAd K outer scalar

def workEnvelope (s K : ℕ) : ℕ :=
  let H := expressionHeightBudget (max s (K+2)) 68
  BinaryReflectedLowerFactoryMeasured.workEnvelope s K+
    BinaryCategoricalLowerMeasured.workEnvelope 18 H+BinaryReflectedEmissionMeasured.workEnvelope H K+12

def envelope (s K : ℕ) : ℕ :=
  let H := expressionHeightBudget (max s (K+2)) 68
  BinaryReflectedLowerFactoryMeasured.envelope s K+
    BinaryCategoricalLowerLifetime.envelope 18 H+BinaryReflectedEmissionMeasured.envelope H K+128

theorem collect_bounds (prepared : (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ)
    (selected : (Fin 18 × Trace) × ℕ) (emitted : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (P S E U V W : ℕ)
    (hP : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ U) (hS : selected.2 ≤ S ∧ usage selected.1.2 ≤ V)
    (hE : emitted.2 ≤ E ∧ usage emitted.1.2 ≤ W) :
    (collect prepared selected emitted).2 ≤ P+S+E+12 ∧ usage (collect prepared selected emitted).1.2 ≤ U+V+W+128 := by
  have hw := wrap_usage 40 3 [prepared.1.2,selected.1.2,emitted.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change prepared.2+selected.2+emitted.2+12 ≤ _ ∧ usage (wrap 40 3 [prepared.1.2,selected.1.2,emitted.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem sample_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (sample input hC hAd K outer scalar).2 ≤ workEnvelope s K ∧ usage (sample input hC hAd K outer scalar).1.2 ≤ envelope s K := by
  let prepared := BinaryReflectedLowerFactoryMeasured.prepared input hC hAd K outer
  let selected := BinaryCategoricalLowerMeasured.segment prepared.1.1 0
  let emitted := BinaryReflectedEmissionMeasured.sample input prepared.1.1.table selected.1.1 K scalar
  let H := expressionHeightBudget (max s (K+2)) 68
  let tableSource := (BinaryTerminalFallback.terminal input source hC hR hCase).profile K outer
  have hRef : prepared.1.1.table.Refines tableSource := by
    rw [BinaryReflectedLowerFactoryMeasured.prepared_table]
    exact BinaryTerminalFallback.table_refines input source hC hR hCase K outer
  have hHeight : tableSource.HeightAt H :=
    BinaryReflectedFallbackHeight.profile_height input source hC hR hCase s hs hH K outer
  have hsH : 3 ≤ H := by unfold H expressionHeightBudget; omega
  have hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) H := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ 68))
  have hEndpoint : ∀ slot j,RationalHeight (value ((prepared.1.1.table.P.read slot).read j)) H ∧
      RationalHeight (value ((prepared.1.1.table.Q.read slot).read j)) H := by
    intro slot j
    rw [hRef.2.1 slot j,hRef.2.2 slot j]
    exact hHeight.2 slot j
  have hP := BinaryReflectedLowerFactoryMeasured.prepared_bounds input source hC hR hCase hAd s hs hH K outer
  have hS := BinaryCategoricalLowerMeasured.segment_bounds prepared.1.1 tableSource hRef H hHeight.1 0
  have hE := BinaryReflectedEmissionMeasured.sample_bounds input hC prepared.1.1.table prepared.1.1.canonical
    H hsH hEndpoint hLengths selected.1.1 K scalar
  have hResult := collect_bounds prepared selected emitted _ _ _ _ _ _ hP hS hE
  rw [sample_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (sample input hC hAd K outer scalar).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((sample input hC hAd K outer scalar).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sample_bounds input source hC hR hCase hAd s hs hH K outer scalar).2 borrowed steps

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j,CanonicalWord ((sample input hC hAd K outer scalar).1.1.read j) := by
  rw [sample_erasure]
  exact BinaryTerminalFallback.sample_canonical input hC hAd K outer scalar

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input hC hAd K outer scalar).1.1.read j) : ℝ)) := by
  rw [sample_erasure]
  exact BinaryTerminalFallback.sample_fullBudget input source hC hAd hR hCase K outer scalar

theorem sample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((sample input hC hAd K outer scalar).1.1.read j) : ℝ)) := by
  rw [sample_erasure]
  exact BinaryTerminalFallback.sample_inBox input source hC hAd hR hCase K outer scalar

end Blotto.BinaryReflectedLowerSampleMeasured
