import Blotto.BinaryReflectedTerminalPrefixMeasured
import Blotto.BinaryFourGluingMeasuredPolynomial
import Blotto.BinaryPRGHeapResourceThreePolynomial

/-! Original fields and incoming seed parameters derive uniform polynomials for
measured reflected preparation, the current physical-resource source charge and
measured terminal input. Nested factories and complete native model costs remain. -/
namespace Blotto.BinaryReflectedPrefixMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3000000

def jointEnvelope (s i cap : ℕ) : ℕ :=
  BinaryReflectedTerminalPrefixMeasured.workEnvelope s i cap+BinaryReflectedTerminalPrefixMeasured.envelope s i cap

theorem work_le_joint (s i cap : ℕ) :
    BinaryReflectedTerminalPrefixMeasured.workEnvelope s i cap ≤ jointEnvelope s i cap := by unfold jointEnvelope; omega

theorem usage_le_joint (s i cap : ℕ) :
    BinaryReflectedTerminalPrefixMeasured.envelope s i cap ≤ jointEnvelope s i cap := by unfold jointEnvelope; omega

macro "unfold_measured_reflected_prefix" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryReflectedTerminalPrefixMeasured.workEnvelope,BinaryReflectedTerminalPrefixMeasured.envelope,
    BinaryReflectedTerminalPrefixMeasured.widthEnvelope,BinaryReflectedResourceMeasured.workEnvelope,BinaryReflectedResourceMeasured.envelope,
    BinaryReflectedPreparationMeasured.workEnvelope,BinaryReflectedPreparationMeasured.envelope,
    BinaryReflectedSystemMeasured.workEnvelope,BinaryReflectedSystemMeasured.envelope,
    BinaryReflectedSystemMeasured.capacityPrice,BinaryReflectedSystemMeasured.capacityEnvelope,BinaryReflectedSystemMeasured.opcodePrice,
    BinaryReflectedTerminalInputMeasured.terminalPrice,BinaryReflectedTerminalInputMeasured.endpointPrice,
    BinaryReflectedFocusMeasured.focusPrice,BinaryReflectedFocusMeasured.fractionalPrice,
    BinaryReflectedTerminalInputLifetime.terminalEnvelope,BinaryReflectedTerminalInputLifetime.endpointEnvelope,
    BinaryReflectedFocusLifetime.focusEnvelope,BinaryReflectedFocusLifetime.fractionalEnvelope,
    BinaryThreeGeometryLifetime.comparisonEnvelope,BinaryLifetimeUsage.opcodeEnvelope,
    BinaryFourParametersMeasured.workEnvelope,BinaryFourParametersMeasured.expressionWork,
    BinaryFourParametersMeasured.envelope,BinaryFourParametersMeasured.expressionCells,BinaryFourParametersMeasured.expressionFrames]
  <;> unfold_measured_group_factory
  <;> unfold_native_lifetime_envelope
  <;> unfold_heap_lifetime_envelope
  <;> simp only [BinaryPRGHeapResourceThreeSource.bound,BinaryPRGHeapResourceThreeSource.loopBound,
    BinaryPRGHeapResourceThreeSource.heapCap,BinaryPRGHeapResourceThreeSource.initialCells,BinaryPRGHeapResourceThreeSource.inputWidth,
    BinaryPRGHeapResourceInputBounds.preparationBound,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGHeapResourceThreeReservation.stepBound,BinaryPRGHeapResourceThreeStep.pairBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,BinaryThreeResourceHeight.coinWidth,BinaryThreeResourceHeight.resourceHeight,
    BinaryPRGHeapResourceUpdateBudget.updateBound,BinaryPRGHeapResourceUpdateBudget.scanBound,BinaryPRGHeapResourceUpdateBudget.testBound,
    BinaryPRGHeapResourceSourceReservation.terminalBound,BinaryPRGWordControllerBooleanResourcePair.bound,
    BinaryPRGWordControllerPairOutputWork.traceBound,BinaryPRGWordControllerPairRegisters.instructionBound,
    BinaryPRGHeapStoredTree.readBound,BinaryPRGWordStoreHeapMachine.lookupBound,BinaryPRGWordStoreHeapMachine.patchBound,
    BinaryPRGWordStoreHeapMachine.readBound,BinaryPRGWordStoreHeapMachine.skipBound,BinaryPRGWordStoreHeapMachine.allocationBound,
    BinaryPRGWordStoreHeap.heapBound,BinaryWordIndexCoinController.sampleBound,BinaryWordIndexCoinController.allowance])

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_reflected_prefix
  resource_polynomial

theorem joint_mono {s i cap t I B : ℕ} (hs : s ≤ t) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s i cap ≤ jointEnvelope t I B := by
  unfold_measured_reflected_prefix
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
    (BinaryReflectedTerminalPrefixMeasured.run store input hC pc hp).2 ≤ C*(s+store.width+store.cap.value+2)^d ∧
      usage (BinaryReflectedTerminalPrefixMeasured.run store input hC pc hp).1.2 ≤ C*(s+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp
  have h := BinaryReflectedTerminalPrefixMeasured.run_bounds store input source hC hR hCase s hs hH pc hp
  have hb := hBound s store.width store.cap.value
  exact ⟨h.1.trans ((work_le_joint _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryReflectedTerminalPrefixMeasured.run store input hC pc hp).1.2 steps ≤
      borrowed+C*(s+store.width+store.cap.value+2)^d ∧
    framePeak ((BinaryReflectedTerminalPrefixMeasured.run store input hC pc hp).1.2.take steps) ≤ C*(s+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase s hs hH pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase s hs hH pc hp).2 borrowed steps

end Blotto.BinaryReflectedPrefixMeasuredPolynomial
