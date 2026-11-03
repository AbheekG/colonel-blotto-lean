import Blotto.BinaryFourSmallMeasured
import Blotto.BinaryReflectedLowerSampleMeasured
import Blotto.BinaryFourSmallFixedLifetime

/-! The measured small-root draw executes deterministic measured physical
fallback only on exhaustion, preserving the actual returned absolute cursor.
Every remaining word window produces the original bounded-sampler row. -/
namespace Blotto.BinaryFourSmallFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  let drawn := BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp
  match drawn.1.1.1 with
  | some row => (((row,drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2+4)
  | none =>
      let fallback := BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar
      (((fallback.1.1,drawn.1.1.2),wrap 32 2 [drawn.1.2,fallback.1.2]),drawn.2+fallback.2+8)

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 =
      (BinaryFourSmallFixedLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 := by
  simp only [run,BinaryFourSmallFixedLifetime.runWithTrace,BinaryFourSmallMeasured.run_data,
    BinaryReflectedLowerSampleMeasured.sample_data]
  cases (BinaryFourSmallLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1.1 with
  | none => exact Prod.ext (BinaryReflectedLowerSampleMeasured.sample_data input hC hAd K outer scalar) rfl
  | some row => rfl

theorem run_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.1 =
      BinarySmallRootSample.fixedSample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  rw [run_data]
  exact BinaryFourSmallFixedLifetime.runWithTrace_window store input hC hAd K outer scalar pc hp

theorem run_cursor (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.2 =
      (BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp).1.1.2 := by
  unfold run
  dsimp only
  split <;> rfl

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_cursor]
  exact BinaryFourSmallMeasured.run_position store input hC hAd K outer scalar pc hp

def workEnvelope (s K i cap : ℕ) : ℕ :=
  BinaryFourSmallMeasured.workEnvelope s K i cap+BinaryReflectedLowerSampleMeasured.workEnvelope s K+8

def envelope (s K i cap : ℕ) : ℕ :=
  BinaryFourSmallMeasured.envelope s K i cap+BinaryReflectedLowerSampleMeasured.envelope s K+128

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K outer scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let drawn := BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp
  have hD := BinaryFourSmallMeasured.run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have hF := BinaryReflectedLowerSampleMeasured.sample_bounds input source hC hR hCase hAd s (by omega) hH K outer scalar
  change drawn.2 ≤ _ ∧ usage drawn.1.2 ≤ _ at hD
  unfold run
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change drawn.2+4 ≤ _ ∧ usage (wrap 24 2 [drawn.1.2]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩
  · let fallback := BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar
    have hw := wrap_usage 32 2 [drawn.1.2,fallback.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change fallback.2 ≤ _ ∧ usage fallback.1.2 ≤ _ at hF
    change drawn.2+fallback.2+8 ≤ _ ∧ usage (wrap 32 2 [drawn.1.2,fallback.1.2]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤
      borrowed+envelope s K store.width store.cap.value ∧
    framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).2 borrowed steps

theorem run_canonical (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    ∀ j,CanonicalWord ((run store input hC hAd K outer scalar pc hp).1.1.1.read j) := by
  rw [run_data]
  exact BinaryFourSmallFixedLifetime.runWithTrace_canonical store input hC hAd K outer scalar pc hp

theorem run_fullBudget (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    FullBudget (source.B : ℝ)
      (fun j => (value ((run store input hC hAd K outer scalar pc hp).1.1.1.read j) : ℝ)) := by
  rw [run_data]
  exact BinaryFourSmallFixedLifetime.runWithTrace_fullBudget store input source hC hR hCase hAd K outer scalar pc hp

theorem run_inBox (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((run store input hC hAd K outer scalar pc hp).1.1.1.read j) : ℝ)) := by
  rw [run_data]
  exact BinaryFourSmallFixedLifetime.runWithTrace_inBox store input source hC hR hCase hAd K outer scalar pc hp

end Blotto.BinaryFourSmallFixedMeasured
