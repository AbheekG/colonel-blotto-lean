import Blotto.BinaryFourGluingDrawMeasured
import Blotto.BinaryFourOrderMeasured
import Blotto.BinaryFourSmallCoinMeasured
import Blotto.BinaryFourGuardMeasured
import Blotto.BinaryWordDrawMeasuredPolynomial

/-! Original six-field heights and seed parameters derive uniform polynomial
source work and retained-prefix bounds for measured gluing. The guard is a
stated gluing-branch condition. Small-root descendants, complete terminal
adoption and native machine realization remain separate. -/

namespace Blotto.BinaryFourGluingMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 4500000

def jointEnvelope (s K i cap : ℕ) : ℕ :=
  BinaryFourGluingDrawMeasured.workEnvelope s K i cap+BinaryFourGluingDrawMeasured.envelope s K i cap+
  BinaryFourOrderMeasured.workEnvelope s+BinaryFourOrderLifetime.orderedEnvelope s+
  BinaryFourSmallCoinMeasured.workEnvelope s i cap+BinaryFourSmallCoinLifetime.envelope s i cap+
  BinaryFourGuardMeasured.workEnvelope s+BinaryFourGuardLifetime.envelope s

theorem work_le_joint (s K i cap : ℕ) :
    BinaryFourGluingDrawMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  unfold jointEnvelope
  omega

theorem usage_le_joint (s K i cap : ℕ) :
    BinaryFourGluingDrawMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  unfold jointEnvelope
  omega

macro "unfold_measured_four_gluing" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryFourGluingDrawMeasured.workEnvelope,BinaryFourGluingDrawMeasured.envelope,
    BinaryFourGluingMeasured.workEnvelope,BinaryFourGluingMeasured.envelope,
    BinaryFourGluingParentsMeasured.workEnvelope,BinaryFourGluingParentsMeasured.envelope,
    BinaryFourParametersMeasured.workEnvelope,BinaryFourParametersMeasured.expressionWork,
    BinaryFourParametersMeasured.envelope,BinaryFourParametersMeasured.expressionCells,BinaryFourParametersMeasured.expressionFrames,
    BinaryOverlapGluingMeasured.workEnvelope,BinaryOverlapGluingMeasured.envelope,
    BinaryOverlapGluingMeasured.slotPrice,BinaryOverlapGluingMeasured.slotEnvelope,
    BinaryOverlapGluingMeasured.expressionWork,BinaryOverlapGluingMeasured.expressionCells,BinaryOverlapGluingMeasured.expressionFrames,
    BinaryFourOrderMeasured.workEnvelope,BinaryFourOrderLifetime.orderedEnvelope,
    BinaryFourOrderLifetime.sortEnvelope,BinaryFourOrderLifetime.compareEnvelope,
    BinaryFourSmallCoinMeasured.workEnvelope,BinaryFourSmallCoinLifetime.envelope,
    BinaryFourGuardMeasured.workEnvelope,BinaryFourGuardLifetime.envelope,
    BinaryWordCoinMeasured.samplePrice,BinaryWordCoinMeasured.localPrice,BinaryLifetimeArrayMeasured.storageReserve]
  <;> unfold_measured_draw_work)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_four_gluing
  resource_polynomial

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  unfold_measured_four_gluing
  unfold expressionHeightBudget
  gcongr

theorem joint_polynomial : ∃ C d : ℕ, ∀ s K i cap,jointEnvelope s K i cap ≤ C*(s+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s K i cap
  let T := s+K+i+cap
  have hm : jointEnvelope s K i cap ≤ jointEnvelope T T T T :=
    joint_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega)
      (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_work : ∃ C d : ℕ, ∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp
  have h := (BinaryFourGluingDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).1
  have hb := hBound s K store.width store.cap.value
  unfold jointEnvelope at hb
  omega

theorem source_all_prefix : ∃ C d : ℕ, ∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).1.2 steps ≤
      borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
    framePeak ((BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).1.2.take steps) ≤
      C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp borrowed steps
  have h := (BinaryFourGluingDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).2
  have hb := hBound s K store.width store.cap.value
  have hUsage : usage (BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).1.2 ≤
      C*(s+K+store.width+store.cap.value+2)^d := by unfold jointEnvelope at hb; omega
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ hUsage borrowed steps

end Blotto.BinaryFourGluingMeasuredPolynomial
