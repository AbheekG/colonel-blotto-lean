import Blotto.BinaryFourRestoredMeasured
import Blotto.BinarySmallUniformMeasuredPolynomial
import Blotto.BinaryReflectedDrawMeasuredPolynomial

/-! Complete measured four-variable optional draws have uniform polynomial
source-work and retained-usage bounds from original fields and seed parameters.
The majorant composes the already proved gluing, uniform and reflected bounds.
Fixed exhaustion fallbacks and full native machine joins remain separate. -/
namespace Blotto.BinaryFourMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 1200000

def jointEnvelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasuredPolynomial.jointEnvelope s K i cap+
  BinarySmallUniformMeasuredPolynomial.jointEnvelope s K i cap+BinaryReflectedDrawMeasuredPolynomial.jointEnvelope s K i cap+5000

theorem joined_le_joint (s K i cap : ℕ) : BinaryFourRestoredMeasured.workEnvelope s K i cap+BinaryFourRestoredMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have hr := BinaryReflectedDrawMeasuredPolynomial.joined_le_joint s K i cap
  simp only [BinaryFourRestoredMeasured.workEnvelope,BinaryFourRestoredMeasured.envelope,
    BinaryFourOrderedMeasured.workEnvelope,BinaryFourOrderedMeasured.envelope,
    BinaryFourSmallMeasured.workEnvelope,BinaryFourSmallMeasured.envelope,jointEnvelope,
    BinaryFourGluingMeasuredPolynomial.jointEnvelope,BinarySmallUniformMeasuredPolynomial.jointEnvelope]
  omega

theorem restored_work_le_joint (s K i cap : ℕ) : BinaryFourRestoredMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem restored_usage_le_joint (s K i cap : ℕ) : BinaryFourRestoredMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem ordered_work_le_joint (s K i cap : ℕ) : BinaryFourOrderedMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := restored_work_le_joint s K i cap; unfold BinaryFourRestoredMeasured.workEnvelope at h; omega

theorem ordered_usage_le_joint (s K i cap : ℕ) : BinaryFourOrderedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := restored_usage_le_joint s K i cap; unfold BinaryFourRestoredMeasured.envelope at h; omega

theorem small_work_le_joint (s K i cap : ℕ) : BinaryFourSmallMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := ordered_work_le_joint s K i cap; unfold BinaryFourOrderedMeasured.workEnvelope at h; omega

theorem small_usage_le_joint (s K i cap : ℕ) : BinaryFourSmallMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := ordered_usage_le_joint s K i cap; unfold BinaryFourOrderedMeasured.envelope at h; omega

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) :=
  NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add BinaryFourGluingMeasuredPolynomial.diagonal_polynomial
      BinarySmallUniformMeasuredPolynomial.diagonal_polynomial) BinaryReflectedDrawMeasuredPolynomial.diagonal_polynomial)
    (NaturalPolynomialEnvelope.constant inputSize 5000)

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  have hg := BinaryFourGluingMeasuredPolynomial.joint_mono hs hk hi hb
  have hu := BinarySmallUniformMeasuredPolynomial.joint_mono hs hk hi hb
  have hr := BinaryReflectedDrawMeasuredPolynomial.joint_mono hs hk hi hb
  unfold jointEnvelope
  omega

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

theorem ordered_source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s → ∀ (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp
  have h := BinaryFourOrderedMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((ordered_work_le_joint _ _ _ _).trans hb),h.2.trans ((ordered_usage_le_joint _ _ _ _).trans hb)⟩

theorem restored_source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s → ∀ (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp
  have h := BinaryFourRestoredMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((restored_work_le_joint _ _ _ _).trans hb),h.2.trans ((restored_usage_le_joint _ _ _ _).trans hb)⟩

theorem restored_source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s → ∀ (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
      framePeak ((BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := restored_source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourMeasuredPolynomial
