import Blotto.BinaryFourGluingFixedMeasured
import Blotto.BinaryFourGluingMeasuredPolynomial

/-! Original fields and scalar/choice parameters bound complete measured fixed
gluing draws, including deterministic lower fallback, by a uniform polynomial.
This combines the existing gluing envelope with actual measured lower work. -/
namespace Blotto.BinaryFourGluingFixedMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 1500000

def extraEnvelope (s K : ℕ) : ℕ := BinaryWordSegmentFixedMeasured.lowerPrice 4 81 (expressionHeightBudget s 36) K+
  BinaryWordSegmentFixedLifetime.lowerEnvelope 4 81 (expressionHeightBudget s 36) K

def jointEnvelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasuredPolynomial.jointEnvelope s K i cap+extraEnvelope s K+256

theorem joined_le_joint (s K i cap : ℕ) : BinaryFourGluingFixedMeasured.workEnvelope s K i cap+BinaryFourGluingFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  simp only [jointEnvelope,extraEnvelope,BinaryFourGluingFixedMeasured.workEnvelope,BinaryFourGluingFixedMeasured.envelope,
    BinaryWordSegmentFixedMeasured.workEnvelope,BinaryWordSegmentFixedLifetime.envelope,
    BinaryFourGluingMeasuredPolynomial.jointEnvelope,BinaryFourGluingDrawMeasured.workEnvelope,BinaryFourGluingDrawMeasured.envelope]
  omega

theorem work_le_joint (s K i cap : ℕ) : BinaryFourGluingFixedMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem usage_le_joint (s K i cap : ℕ) : BinaryFourGluingFixedMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

macro "unfold_measured_fixed_gluing_extra" : tactic => `(tactic|
  simp only [extraEnvelope,BinaryWordSegmentFixedMeasured.lowerPrice,BinaryCategoricalLowerMeasured.workEnvelope,
    BinaryCategoricalLowerMeasured.sourcePreparationPrice,BinaryWordSegmentFixedLifetime.lowerEnvelope,
    BinaryCategoricalLowerLifetime.envelope,BinaryCategoricalLowerLifetime.sourcePreparationEnvelope,
    BinaryPhysicalPointMeasured.price,BinaryTapePointLifetime.bound,BinaryQuadraticExpression.uniformPrice]
  <;> unfold_word_terminal_envelope)

theorem extra_diagonal : NaturalPolynomialEnvelope inputSize (fun p => extraEnvelope p.wordWidth p.wordWidth) := by
  unfold_measured_fixed_gluing_extra
  resource_polynomial

theorem extra_mono {s K t T : ℕ} (hs : s ≤ t) (hk : K ≤ T) : extraEnvelope s K ≤ extraEnvelope t T := by
  unfold_measured_fixed_gluing_extra
  unfold expressionHeightBudget
  gcongr

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) :=
  NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add BinaryFourGluingMeasuredPolynomial.diagonal_polynomial extra_diagonal)
    (NaturalPolynomialEnvelope.constant inputSize 256)

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  have hg := BinaryFourGluingMeasuredPolynomial.joint_mono hs hk hi hb
  have he := extra_mono hs hk
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

theorem source_bounds : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryFourGluingFixedMeasured.run store input hC hAd K scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryFourGluingFixedMeasured.run store input hC hAd K scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp
  have h := BinaryFourGluingFixedMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((work_le_joint _ _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ),3 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryFourGluingFixedMeasured.run store input hC hAd K scalar pc hp).1.2 steps ≤ borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
      framePeak ((BinaryFourGluingFixedMeasured.run store input hC hAd K scalar pc hp).1.2.take steps) ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

end Blotto.BinaryFourGluingFixedMeasuredPolynomial
