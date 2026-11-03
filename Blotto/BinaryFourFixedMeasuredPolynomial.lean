import Blotto.BinaryFourRestoredFixedMeasured
import Blotto.BinarySmallUniformMeasuredPolynomial
import Blotto.BinaryReflectedDrawMeasuredPolynomial

import Blotto.BinaryFourMeasuredPolynomial
import Blotto.BinaryFourGluingFixedMeasuredPolynomial
import Blotto.BinaryReflectedLowerMeasuredPolynomial

/-! Complete measured fixed four-variable draws include every deterministic
exhaustion fallback, sorting, guard/root dispatch and inverse row restoration.
Original fields and seed/scalar parameters derive uniform polynomial source
work and every-prefix storage. Complete native-machine joins remain open. -/
namespace Blotto.BinaryFourFixedMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def jointEnvelope (s K i cap : ℕ) : ℕ := BinaryFourMeasuredPolynomial.jointEnvelope s K i cap+
  BinaryFourGluingFixedMeasuredPolynomial.extraEnvelope s K+BinaryReflectedLowerMeasuredPolynomial.jointEnvelope s K+1024

theorem joined_le_joint (s K i cap : ℕ) : BinaryFourRestoredFixedMeasured.workEnvelope s K i cap+BinaryFourRestoredFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have hOld := BinaryFourMeasuredPolynomial.joined_le_joint s K i cap
  have hGluing : BinaryFourGluingFixedMeasured.workEnvelope s K i cap+BinaryFourGluingFixedMeasured.envelope s K i cap ≤
      BinaryFourGluingDrawMeasured.workEnvelope s K i cap+BinaryFourGluingDrawMeasured.envelope s K i cap+
        BinaryFourGluingFixedMeasuredPolynomial.extraEnvelope s K+256 := by
    simp only [BinaryFourGluingFixedMeasured.workEnvelope,BinaryFourGluingFixedMeasured.envelope,
      BinaryFourGluingDrawMeasured.workEnvelope,BinaryFourGluingDrawMeasured.envelope,
      BinaryWordSegmentFixedMeasured.workEnvelope,BinaryWordSegmentFixedLifetime.envelope,
      BinaryFourGluingFixedMeasuredPolynomial.extraEnvelope]
    omega
  have hLower := BinaryReflectedLowerMeasuredPolynomial.joined_le_joint s K
  simp only [jointEnvelope,BinaryFourRestoredFixedMeasured.workEnvelope,BinaryFourRestoredFixedMeasured.envelope,
    BinaryFourOrderedFixedMeasured.workEnvelope,BinaryFourOrderedFixedMeasured.envelope,
    BinaryFourSmallFixedMeasured.workEnvelope,BinaryFourSmallFixedMeasured.envelope,
    BinaryFourRestoredMeasured.workEnvelope,BinaryFourRestoredMeasured.envelope,
    BinaryFourOrderedMeasured.workEnvelope,BinaryFourOrderedMeasured.envelope,
    BinaryFourGluingFixedMeasuredPolynomial.jointEnvelope,BinaryFourGluingMeasuredPolynomial.jointEnvelope] at *
  omega

theorem restored_work_le_joint (s K i cap : ℕ) : BinaryFourRestoredFixedMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem restored_usage_le_joint (s K i cap : ℕ) : BinaryFourRestoredFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem ordered_work_le_joint (s K i cap : ℕ) : BinaryFourOrderedFixedMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := restored_work_le_joint s K i cap; unfold BinaryFourRestoredFixedMeasured.workEnvelope at h; omega

theorem ordered_usage_le_joint (s K i cap : ℕ) : BinaryFourOrderedFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := restored_usage_le_joint s K i cap; unfold BinaryFourRestoredFixedMeasured.envelope at h; omega

theorem small_work_le_joint (s K i cap : ℕ) : BinaryFourSmallFixedMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := ordered_work_le_joint s K i cap; unfold BinaryFourOrderedFixedMeasured.workEnvelope at h; omega

theorem small_usage_le_joint (s K i cap : ℕ) : BinaryFourSmallFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := ordered_usage_le_joint s K i cap; unfold BinaryFourOrderedFixedMeasured.envelope at h; omega

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) :=
  NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add BinaryFourMeasuredPolynomial.diagonal_polynomial
      BinaryFourGluingFixedMeasuredPolynomial.extra_diagonal) BinaryReflectedLowerMeasuredPolynomial.diagonal_polynomial)
    (NaturalPolynomialEnvelope.constant inputSize 1024)

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  have hOld := BinaryFourMeasuredPolynomial.joint_mono hs hk hi hb
  have hGluing := BinaryFourGluingFixedMeasuredPolynomial.extra_mono hs hk
  have hLower := BinaryReflectedLowerMeasuredPolynomial.joint_mono hs hk
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
    (BinaryFourOrderedFixedMeasured.run store input hC hAd K outer scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourOrderedFixedMeasured.run store input hC hAd K outer scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp
  have h := BinaryFourOrderedFixedMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((ordered_work_le_joint _ _ _ _).trans hb),h.2.trans ((ordered_usage_le_joint _ _ _ _).trans hb)⟩

theorem restored_source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s → ∀ (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourRestoredFixedMeasured.run store input hC hAd K outer scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourRestoredFixedMeasured.run store input hC hAd K outer scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp
  have h := BinaryFourRestoredFixedMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((restored_work_le_joint _ _ _ _).trans hb),h.2.trans ((restored_usage_le_joint _ _ _ _).trans hb)⟩

theorem restored_source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ),3 ≤ s → source.FieldsHeight s → ∀ (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryFourRestoredFixedMeasured.run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
      framePeak ((BinaryFourRestoredFixedMeasured.run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := restored_source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hAd s hs hH K outer scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourFixedMeasuredPolynomial
