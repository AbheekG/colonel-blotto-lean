import Blotto.BinaryReflectedLowerSampleMeasured
import Blotto.BinaryReflectedDrawMeasuredPolynomial

/-! Original reflected fields and scalar precision give a uniform polynomial
for deterministic fallback's joined source work and all-prefix storage. The
physical lower components reuse the stronger random-source price at zero seed
parameters only as an erased numerical majorant. No random run or coin occurs
in this deterministic producer. Native machine/model joins remain open. -/
namespace Blotto.BinaryReflectedLowerMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3000000

def suffixEnvelope (s K : ℕ) : ℕ :=
  let H := expressionHeightBudget (max s (K+2)) 68
  BinaryCategoricalLowerMeasured.workEnvelope 18 H+BinaryCategoricalLowerLifetime.envelope 18 H+
    BinaryReflectedEmissionMeasured.workEnvelope H K+BinaryReflectedEmissionMeasured.envelope H K

def jointEnvelope (s K : ℕ) : ℕ :=
  BinaryReflectedProfileMeasuredPolynomial.jointEnvelope s 0 0 K+suffixEnvelope s K+140000

theorem joined_le_joint (s K : ℕ) :
    BinaryReflectedLowerSampleMeasured.workEnvelope s K+BinaryReflectedLowerSampleMeasured.envelope s K ≤ jointEnvelope s K := by
  simp only [jointEnvelope,suffixEnvelope,BinaryReflectedLowerSampleMeasured.workEnvelope,BinaryReflectedLowerSampleMeasured.envelope,
    BinaryReflectedLowerFactoryMeasured.workEnvelope,BinaryReflectedLowerFactoryMeasured.envelope,
    BinaryReflectedLowerMeasured.workEnvelope,BinaryReflectedLowerMeasured.envelope,
    BinaryPRGHeapLowerSourceMeasured.workEnvelope,BinaryPRGHeapLowerSourceBound.envelope,
    BinaryReflectedTerminalFactoryMeasured.workEnvelope,BinaryReflectedTerminalFactoryMeasured.envelope,
    BinaryReflectedProfileMeasuredPolynomial.jointEnvelope,
    BinaryReflectedProfilePrefixMeasured.workEnvelope,BinaryReflectedProfilePrefixMeasured.envelope,
    BinaryReflectedTerminalPrefixMeasured.workEnvelope,BinaryReflectedTerminalPrefixMeasured.envelope,
    BinaryReflectedTerminalPrefixMeasured.widthEnvelope,
    BinaryReflectedResourceMeasured.workEnvelope,BinaryReflectedResourceMeasured.envelope,
    BinaryPRGHeapResourceThreeSource.bound,BinaryPRGHeapThreeNativeLifetimeBound.envelope]
  omega

theorem work_le_joint (s K : ℕ) : BinaryReflectedLowerSampleMeasured.workEnvelope s K ≤ jointEnvelope s K := by
  have h := joined_le_joint s K; omega

theorem usage_le_joint (s K : ℕ) : BinaryReflectedLowerSampleMeasured.envelope s K ≤ jointEnvelope s K := by
  have h := joined_le_joint s K; omega

macro "unfold_measured_reflected_lower_suffix" : tactic => `(tactic|
  simp only [suffixEnvelope,BinaryCategoricalLowerMeasured.workEnvelope,
    BinaryCategoricalLowerMeasured.sourcePreparationPrice,BinaryCategoricalLowerLifetime.envelope,
    BinaryCategoricalLowerLifetime.sourcePreparationEnvelope,BinaryQuadraticExpression.uniformPrice,
    BinaryReflectedEmissionMeasured.workEnvelope,BinaryReflectedEmissionMeasured.envelope,
    BinaryReflectedEmissionMeasured.reflectPrice,BinaryReflectedEmissionMeasured.reflectEnvelope,
    BinaryReflectedEmissionMeasured.widthEnvelope,BinaryQuadraticPointOutputLifetime.rowWidth,
    BinaryReflectedSystemMeasured.opcodePrice,BinaryPhysicalPointMeasured.price,BinaryTapePointLifetime.bound]
  <;> unfold_word_terminal_envelope)

theorem suffix_diagonal : NaturalPolynomialEnvelope inputSize (fun p => suffixEnvelope p.wordWidth p.wordWidth) := by
  unfold_measured_reflected_lower_suffix
  resource_polynomial

theorem suffix_mono {s K t T : ℕ} (hs : s ≤ t) (hk : K ≤ T) : suffixEnvelope s K ≤ suffixEnvelope t T := by
  unfold_measured_reflected_lower_suffix
  unfold expressionHeightBudget
  gcongr

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth) := by
  have hPrefix : NaturalPolynomialEnvelope inputSize
      (fun p => BinaryReflectedProfileMeasuredPolynomial.jointEnvelope p.wordWidth 0 0 p.wordWidth) :=
    NaturalPolynomialEnvelope.dominated BinaryReflectedProfileMeasuredPolynomial.diagonal_polynomial
      (fun _ => BinaryReflectedProfileMeasuredPolynomial.joint_mono le_rfl (Nat.zero_le _) (Nat.zero_le _) le_rfl)
  exact NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add hPrefix suffix_diagonal)
    (NaturalPolynomialEnvelope.constant inputSize 140000)

theorem joint_mono {s K t T : ℕ} (hs : s ≤ t) (hk : K ≤ T) : jointEnvelope s K ≤ jointEnvelope t T := by
  have hPrefix := BinaryReflectedProfileMeasuredPolynomial.joint_mono hs (le_refl 0) (le_refl 0) hk
  have hSuffix := suffix_mono hs hk
  unfold jointEnvelope
  omega

theorem joint_polynomial : ∃ C d : ℕ,∀ s K,jointEnvelope s K ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s K
  let T := s+K
  have hm : jointEnvelope s K ≤ jointEnvelope T T := joint_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_bounds : ∃ C d : ℕ,∀ (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K),
    (BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar).2 ≤ C*(s+K+2)^d ∧
      usage (BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar).1.2 ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro input source hC hR hCase hAd s hs hH K outer scalar
  have h := BinaryReflectedLowerSampleMeasured.sample_bounds input source hC hR hCase hAd s hs hH K outer scalar
  have hb := hBound s K
  exact ⟨h.1.trans ((work_le_joint _ _).trans hb),h.2.trans ((usage_le_joint _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar).1.2 steps ≤ borrowed+C*(s+K+2)^d ∧
      framePeak ((BinaryReflectedLowerSampleMeasured.sample input hC hAd K outer scalar).1.2.take steps) ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro input source hC hR hCase hAd s hs hH K outer scalar borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound input source hC hR hCase hAd s hs hH K outer scalar).2 borrowed steps

end Blotto.BinaryReflectedLowerMeasuredPolynomial
