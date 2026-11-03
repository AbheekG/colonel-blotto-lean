import Blotto.BinaryFourSmallUniformCoinHandoffMeasured
import Blotto.BinaryFourGluingMeasuredPolynomial

/-! Original six-field heights and seed parameters bound the measured complete
small-uniform factory/draw and its actual root-coin handoff by uniform
polynomials. Reached widths and execution prices are not inputs. Reflected
branches, complete terminal adoption and native model realization remain. -/
namespace Blotto.BinarySmallUniformMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000

def jointEnvelope (s K i cap : ℕ) : ℕ :=
  BinaryFourSmallUniformDrawMeasured.workEnvelope s K i cap+BinaryFourSmallUniformDrawMeasured.envelope s K i cap+
  BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope s K i cap cap+
  BinaryFourSmallUniformCoinHandoffMeasured.envelope s K i cap cap

theorem draw_work_le_joint (s K i cap : ℕ) :
    BinaryFourSmallUniformDrawMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by unfold jointEnvelope; omega

theorem draw_usage_le_joint (s K i cap : ℕ) :
    BinaryFourSmallUniformDrawMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by unfold jointEnvelope; omega

theorem handoff_work_le_joint (s K i cap r : ℕ) (hr : r ≤ cap) :
    BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope s K i cap r ≤ jointEnvelope s K i cap := by
  have hm : BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope s K i cap r ≤
      BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope s K i cap cap := by
    simp only [BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope,BinaryFourSmallCoinMeasured.workEnvelope,
      BinaryWordCoinMeasured.samplePrice]
    gcongr
  unfold jointEnvelope
  omega

theorem handoff_usage_le_joint (s K i cap r : ℕ) (hr : r ≤ cap) :
    BinaryFourSmallUniformCoinHandoffMeasured.envelope s K i cap r ≤ jointEnvelope s K i cap := by
  have hm : BinaryFourSmallUniformCoinHandoffMeasured.envelope s K i cap r ≤
      BinaryFourSmallUniformCoinHandoffMeasured.envelope s K i cap cap := by
    simp only [BinaryFourSmallUniformCoinHandoffMeasured.envelope,BinaryFourSmallCoinLifetime.envelope,
      BinaryWordCoinLifetime.sampleBound,BinaryWordCoinLifetime.localBound]
    gcongr
  unfold jointEnvelope
  omega

macro "unfold_measured_small_uniform" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryFourSmallUniformDrawMeasured.workEnvelope,BinaryFourSmallUniformDrawMeasured.envelope,
    BinaryFourSmallUniformCoinHandoffMeasured.workEnvelope,BinaryFourSmallUniformCoinHandoffMeasured.envelope,
    BinarySmallUniformFactoryMeasured.workEnvelope,BinarySmallUniformFactoryMeasured.envelope,
    BinarySmallUniformPreparationMeasured.workEnvelope,BinarySmallUniformPreparationMeasured.envelope,
    BinarySmallUniformDescriptorMeasured.workEnvelope,BinarySmallUniformDescriptorMeasured.envelope,
    BinarySmallUniformDescriptorMeasured.childPrice,BinarySmallUniformDescriptorMeasured.childEnvelope,
    BinarySmallUniformDescriptorMeasured.arrayPrice,BinarySmallUniformDescriptorMeasured.arrayEnvelope,
    BinarySmallUniformSplitMeasured.workEnvelope,BinarySmallUniformSplitMeasured.envelope,
    BinarySmallUniformSplitMeasured.opcodePrice,BinarySmallUniformSplitLifetime.envelope]
  <;> unfold_measured_four_gluing)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_small_uniform
  resource_polynomial

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  unfold_measured_small_uniform
  unfold expressionHeightBudget
  gcongr

theorem joint_polynomial : ∃ C d : ℕ,∀ s K i cap,jointEnvelope s K i cap ≤ C*(s+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s K i cap
  let T := s+K+i+cap
  have hm : jointEnvelope s K i cap ≤ jointEnvelope T T T T := joint_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_handoff_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourSmallUniformCoinHandoffMeasured.run store input hC hAd K scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourSmallUniformCoinHandoffMeasured.run store input hC hAd K scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp
  have h := BinaryFourSmallUniformCoinHandoffMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((handoff_work_le_joint _ _ _ _ _ (Nat.sub_le _ _)).trans hb),
    h.2.trans ((handoff_usage_le_joint _ _ _ _ _ (Nat.sub_le _ _)).trans hb)⟩

theorem source_handoff_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryFourSmallUniformCoinHandoffMeasured.run store input hC hAd K scalar pc hp).1.2 steps ≤
      borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
    framePeak ((BinaryFourSmallUniformCoinHandoffMeasured.run store input hC hAd K scalar pc hp).1.2.take steps) ≤
      C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_handoff_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

end Blotto.BinarySmallUniformMeasuredPolynomial
