import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedLowerFactoryLifetime
import Blotto.BinaryCategoricalLowerLifetime
import Blotto.BinaryReflectedEmissionLifetime

/-! One actual physical lower resource/table producer feeds deterministic lower
categorical selection and selected interpolation/reflection. Its complete row
is the original fallback, with original-field every-prefix reservations. -/
namespace Blotto.BinaryReflectedLowerSampleLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 2000000

def sampleWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FixedArrayTable 4 SignedWord × Trace :=
  let prepared := BinaryReflectedLowerFactoryLifetime.prepareWithTrace input hC hAd K outer
  let selected := BinaryCategoricalLowerLifetime.segmentWithTrace prepared.1 0
  let emitted := BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.1.table selected.1 K scalar
  (emitted.1,wrap 40 3 [prepared.2,selected.2,emitted.2])

theorem sampleWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (sampleWithTrace input hC hAd K outer scalar).1 = BinaryTerminalFallback.sample input hC hAd K outer scalar := by
  let prepared := BinaryReflectedLowerFactoryLifetime.prepareWithTrace input hC hAd K outer
  have hTable : prepared.1.table = BinaryTerminalFallback.table input hC K outer :=
    BinaryReflectedLowerFactoryLifetime.prepareWithTrace_table input hC hAd K outer
  have hSelected : (BinaryCategoricalLowerLifetime.segmentWithTrace prepared.1 0).1 =
      BinaryTerminalFallback.slot input hC hAd K outer := by
    rw [BinaryCategoricalLowerLifetime.segmentWithTrace_erasure]
    unfold BinaryTerminalFallback.slot
    simp only [hTable]
  unfold sampleWithTrace
  change (BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.1.table
    (BinaryCategoricalLowerLifetime.segmentWithTrace prepared.1 0).1 K scalar).1 = _
  rw [BinaryReflectedEmissionLifetime.sampleWithTrace_erasure input hC _ prepared.1.canonical,hTable,hSelected]
  rfl

def envelope (s K : ℕ) : ℕ :=
  let H := expressionHeightBudget (max s (K+2)) 68
  BinaryReflectedLowerFactoryLifetime.envelope s K+
    BinaryCategoricalLowerLifetime.envelope 18 H+BinaryReflectedEmissionLifetime.envelope H K+128

theorem sampleWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (sampleWithTrace input hC hAd K outer scalar).2 ≤ envelope s K := by
  let prepared := BinaryReflectedLowerFactoryLifetime.prepareWithTrace input hC hAd K outer
  let selected := BinaryCategoricalLowerLifetime.segmentWithTrace prepared.1 0
  let emitted := BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.1.table selected.1 K scalar
  let H := expressionHeightBudget (max s (K+2)) 68
  let tableSource := (BinaryTerminalFallback.terminal input source hC hR hCase).profile K outer
  have hRef : prepared.1.table.Refines tableSource := by
    rw [BinaryReflectedLowerFactoryLifetime.prepareWithTrace_table]
    exact BinaryTerminalFallback.table_refines input source hC hR hCase K outer
  have hHeight : tableSource.HeightAt H :=
    BinaryReflectedFallbackHeight.profile_height input source hC hR hCase s hs hH K outer
  have hsH : 3 ≤ H := by unfold H expressionHeightBudget; omega
  have hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) H := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ 68))
  have hP := BinaryReflectedLowerFactoryLifetime.prepareWithTrace_usage input source hC hR hCase hAd s hs hH K outer
  have hS := BinaryCategoricalLowerLifetime.segmentWithTrace_usage prepared.1 tableSource hRef H hHeight.1 0
  have hE := BinaryReflectedEmissionLifetime.sampleWithTrace_usage input hC prepared.1.table prepared.1.canonical
    tableSource hRef H hsH hHeight hLengths selected.1 K scalar
  have hw := wrap_usage 40 3 [prepared.2,selected.2,emitted.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (sampleWithTrace input hC hAd K outer scalar).2 ≤ _ at hw
  change usage prepared.2 ≤ _ at hP
  change usage selected.2 ≤ _ at hS
  change usage emitted.2 ≤ _ at hE
  change usage (sampleWithTrace input hC hAd K outer scalar).2 ≤
    BinaryReflectedLowerFactoryLifetime.envelope s K+BinaryCategoricalLowerLifetime.envelope 18 H+
      BinaryReflectedEmissionLifetime.envelope H K+128
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace input hC hAd K outer scalar).2 steps ≤ borrowed+envelope s K ∧
      framePeak ((sampleWithTrace input hC hAd K outer scalar).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sampleWithTrace_usage input source hC hR hCase hAd s hs hH K outer scalar) borrowed steps

theorem sampleWithTrace_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j,CanonicalWord ((sampleWithTrace input hC hAd K outer scalar).1.read j) := by
  rw [sampleWithTrace_erasure]
  exact BinaryTerminalFallback.sample_canonical input hC hAd K outer scalar

theorem sampleWithTrace_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithTrace input hC hAd K outer scalar).1.read j) : ℝ)) := by
  rw [sampleWithTrace_erasure]
  exact BinaryTerminalFallback.sample_fullBudget input source hC hAd hR hCase K outer scalar

theorem sampleWithTrace_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((sampleWithTrace input hC hAd K outer scalar).1.read j) : ℝ)) := by
  rw [sampleWithTrace_erasure]
  exact BinaryTerminalFallback.sample_inBox input source hC hAd hR hCase K outer scalar

end Blotto.BinaryReflectedLowerSampleLifetime
