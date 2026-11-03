import Blotto.BinaryFourSmallUniformDrawMeasured
import Blotto.BinaryFourSmallCoinMeasured
import Blotto.BinaryFourSmallUniformCoinHandoffLifetime

/-! The returned measured small-root coin cursor feeds the measured uniform
factory/draw once. This is the true-branch handoff companion, with exact old
branch data and original-field source bounds. The reflected branch and complete
small-root dispatch remain to be joined. Native model realization is separate. -/
namespace Blotto.BinaryFourSmallUniformCoinHandoffMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 500000

def join (store : BinarySeedLookupTree.Store)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (drawn : (BinaryPRGWordControllerFour.Result store × Trace) × ℕ) :
    (BinaryPRGWordControllerFour.Result store × Trace) × ℕ :=
  ((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8)

def afterRoot (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) :
    (BinaryPRGWordControllerFour.Result store × Trace) × ℕ :=
  let drawn := BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar root.1.1.2
    (by rw [hRoot]; exact (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2)
  join store root drawn

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerFour.Result store × Trace) × ℕ :=
  let root := BinaryFourSmallCoinMeasured.sample store input pc hp
  afterRoot store input hC hAd K scalar pc hp root rfl

theorem run_eq (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K scalar pc hp =
      join store (BinaryFourSmallCoinMeasured.sample store input pc hp)
        (BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar
          (BinaryFourSmallCoinMeasured.sample store input pc hp).1.1.2
          (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2) := rfl

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1 =
      (BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace store input hC hAd K scalar pc hp).1 := by
  simp only [run,afterRoot,join,BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace,
    BinaryFourSmallUniformCoinHandoffLifetime.afterRootWithTrace,
    BinaryFourSmallUniformDrawMeasured.run_data,BinaryFourSmallCoinMeasured.sample_erases]

theorem old_true_branch (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (hTrue : (BinaryFourSmallCoinMeasured.sample store input pc hp).1.1.1 = some true) :
    (run store input hC hAd K scalar pc hp).1.1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  rw [run_data]
  apply BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace_old_true_branch
  rw [← BinaryFourSmallCoinMeasured.sample_erases]
  exact hTrue

def workEnvelope (s K i cap remaining : ℕ) : ℕ := BinaryFourSmallCoinMeasured.workEnvelope s i remaining+
  BinaryFourSmallUniformDrawMeasured.workEnvelope s K i cap+8

def envelope (s K i cap remaining : ℕ) : ℕ := BinaryFourSmallCoinLifetime.envelope s i remaining+
  BinaryFourSmallUniformDrawMeasured.envelope s K i cap+64

theorem join_bounds (store : BinarySeedLookupTree.Store)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (drawn : (BinaryPRGWordControllerFour.Result store × Trace) × ℕ) (R D B C : ℕ)
    (hr : root.2 ≤ R ∧ usage root.1.2 ≤ B) (hd : drawn.2 ≤ D ∧ usage drawn.1.2 ≤ C) :
    (join store root drawn).2 ≤ R+D+8 ∧ usage (join store root drawn).1.2 ≤ B+C+64 := by
  have hw := wrap_usage 32 2 [root.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change root.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [root.1.2,drawn.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
      usage (run store input hC hAd K scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  let root := BinaryFourSmallCoinMeasured.sample store input pc hp
  let drawn := BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar root.1.1.2
    (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2
  have hRootW := BinaryFourSmallCoinMeasured.sample_work store input source hC hR s hH pc hp
  have hRootU := BinaryFourSmallCoinLifetime.sampleWithTrace_usage store input source hC hR s hH pc hp
  rw [← BinaryFourSmallCoinMeasured.sample_erases] at hRootU
  have hDraw := BinaryFourSmallUniformDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar root.1.1.2
    (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2
  have hResult := join_bounds store root drawn _ _ _ _ ⟨hRootW,hRootU⟩ hDraw
  rw [run_eq]
  simpa only [root,drawn,workEnvelope,envelope] using hResult

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace_position store input hC hAd K scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K scalar pc hp).1.2 steps ≤
      borrowed+envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
      framePeak ((run store input hC hAd K scalar pc hp).1.2.take steps) ≤
        envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

theorem afterRoot_eq_run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) :
    afterRoot store input hC hAd K scalar pc hp root hRoot = run store input hC hAd K scalar pc hp := by
  subst root
  unfold run
  with_reducible rfl

theorem afterRoot_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) :
    (afterRoot store input hC hAd K scalar pc hp root hRoot).1.1 =
      (BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace store input hC hAd K scalar pc hp).1 := by
  rw [afterRoot_eq_run]
  exact run_data store input hC hAd K scalar pc hp

theorem afterRoot_old_true_branch (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) (hTrue : root.1.1.1 = some true) :
    (afterRoot store input hC hAd K scalar pc hp root hRoot).1.1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  rw [afterRoot_eq_run]
  apply old_true_branch
  rw [← hRoot]
  exact hTrue

theorem afterRoot_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) :
    (afterRoot store input hC hAd K scalar pc hp root hRoot).2 ≤ workEnvelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
      usage (afterRoot store input hC hAd K scalar pc hp root hRoot).1.2 ≤ envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  rw [afterRoot_eq_run]
  exact run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp

theorem afterRoot_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) :
    pc.value ≤ (afterRoot store input hC hAd K scalar pc hp root hRoot).1.1.2.value ∧
      (afterRoot store input hC hAd K scalar pc hp root hRoot).1.1.2.value ≤ store.cap.value := by
  rw [afterRoot_eq_run]
  exact run_position store input hC hAd K scalar pc hp

theorem afterRoot_all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (root : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ)
    (hRoot : root = BinaryFourSmallCoinMeasured.sample store input pc hp) (borrowed steps : ℕ) :
    retainedHeap borrowed (afterRoot store input hC hAd K scalar pc hp root hRoot).1.2 steps ≤
      borrowed+envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((afterRoot store input hC hAd K scalar pc hp root hRoot).1.2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  rw [afterRoot_eq_run]
  exact all_prefix store input source hC hR hCase hAd s hs hH K scalar pc hp borrowed steps

end Blotto.BinaryFourSmallUniformCoinHandoffMeasured
