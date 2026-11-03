import Blotto.BinaryPRGHeapResourceThreePolynomial
import Blotto.BinaryPRGWordControllerReflectedSetupWork

/-! Actual reflected setup and its three-coordinate resource phase execute
the physical original-array backend at the incoming absolute seed cursor.
The original native three-state result and cursor are unchanged. -/

namespace Blotto.BinaryPRGHeapReflectedSetup
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryReflectedFourSetup

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity × ℕ :=
  let prepared := prepare input
  let drawn := BinaryPRGHeapResourceThreeSource.sourceRun store prepared.capacity prepared.initial
    (capacity_canonical prepared (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2 pc hp
  (drawn.1,(BinaryReflectedSetupWork.prepareWithWork input).2 +
    BinaryPRGWordControllerReflectedSetupWork.extraScaleWork input +
    2 * (BinaryReflectedSetupWork.capacityWithWork prepared).2 + drawn.2 + 4)

theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).1 =
      BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp := by
  unfold run BinaryPRGWordControllerThreeResource.setupIndexed
  dsimp only
  exact BinaryPRGHeapResourceThreeSource.sourceRun_erasure _ _ _ _ _ _ _

def bound (s indexWidth seedCap : ℕ) : ℕ :=
  BinaryReflectedSetupWork.bound s + BinaryPRGWordControllerReflectedSetupWork.extraScaleBound s +
    2 * (3 * (12000 * (2 + 2 * expressionHeightBudget s 14)^3)) +
    BinaryPRGHeapResourceThreeSource.bound (expressionHeightBudget s 15) indexWidth seedCap + 4

theorem run_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).2 ≤ bound s store.width store.cap.value := by
  have hSetup := BinaryReflectedSetupWork.prepareWithWork_bound input source hC hR s hs hH
  have hScale := BinaryPRGWordControllerReflectedSetupWork.extraScaleWork_bound input source hC hR s hs hH
  have hCapacity := BinaryReflectedSetupWork.actual_capacityWithWork_bound input source hC hR hCase s hs hH
  have hCap := BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial := BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  have hRun := BinaryPRGHeapResourceThreeSource.sourceRun_bound (expressionHeightBudget s 15)
    (hs.trans (expressionHeightBudget_ge_input s 15)) store (prepare input).capacity (prepare input).initial
    (capacity_canonical _ (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2 hCap hInitial pc hp
  unfold run bound
  dsimp only
  omega

open BinaryPRGHeapResourcePolynomial in
theorem bound_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => bound p.wordWidth p.seedWidth p.seedCap) := by
  simp only [bound,BinaryReflectedSetupWork.bound,BinaryCachedFourParameterWork.parameterBound,
    BinaryPRGWordControllerReflectedSetupWork.extraScaleBound,BinaryRationalExpression.uniformPrice,
    BinaryPRGHeapResourceThreeSource.bound,BinaryPRGHeapResourceThreeSource.loopBound,
    BinaryPRGHeapResourceThreeSource.heapCap,BinaryPRGHeapResourceThreeSource.initialCells,
    BinaryPRGHeapResourceThreeSource.inputWidth,
    BinaryPRGHeapResourceInputBounds.preparationBound,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGHeapResourceThreeReservation.stepBound,BinaryPRGHeapResourceThreeStep.pairBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,
    BinaryThreeResourceHeight.coinWidth,BinaryThreeResourceHeight.resourceHeight,
    BinaryPRGHeapResourceUpdateBudget.updateBound,BinaryPRGHeapResourceUpdateBudget.scanBound,
    BinaryPRGHeapResourceUpdateBudget.testBound,BinaryPRGHeapResourceSourceReservation.terminalBound,
    BinaryPRGWordControllerBooleanResourcePair.bound,BinaryPRGWordControllerPairOutputWork.traceBound,
    BinaryPRGWordControllerPairRegisters.instructionBound,
    BinaryPRGHeapStoredTree.readBound,BinaryPRGWordStoreHeapMachine.lookupBound,
    BinaryPRGWordStoreHeapMachine.patchBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,BinaryPRGWordStoreHeapMachine.allocationBound,
    BinaryPRGWordStoreHeap.heapBound,BinaryWordIndexCoinController.sampleBound,
    BinaryWordIndexCoinController.allowance]
  resource_polynomial

theorem uniform_run_bound : ∃ C d : ℕ,
    ∀ (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
      (hC : input.Canonical), input.Refines source → source.w < (1 - source.p) * source.ell →
      ∀ (s : ℕ),2 ≤ s → source.FieldsHeight s →
      ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
      (run store input hC pc hp).2 ≤ C * (s + store.width + store.cap.value + 2)^d := by
  rcases bound_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp
  have h := (run_bound store input source hC hR hCase s hs hH pc hp).trans
    (hBound ⟨0,s,0,store.width,store.cap.value⟩)
  have he : s + 1 + store.width + store.cap.value + 1 = s + store.width + store.cap.value + 2 := by omega
  simpa only [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth,Nat.log2_zero,Nat.zero_add,he] using h

end Blotto.BinaryPRGHeapReflectedSetup
