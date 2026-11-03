import Blotto.BinaryNestedProfileMeasured
import Blotto.BinaryNestedSecondMeasuredPolynomial

/-! The complete measured nested producer, including boundary/control, all
three selected interior regimes and coordinate restoration, has a uniform
polynomial source envelope in original nested-field height and scalar width. -/
namespace Blotto.BinaryNestedProfileMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3500000

def jointEnvelope (s K : ℕ) : ℕ := BinaryNestedProfileMeasured.workEnvelope s K+BinaryNestedProfileMeasured.envelope s K

theorem work_le_joint (s K : ℕ) : BinaryNestedProfileMeasured.workEnvelope s K ≤ jointEnvelope s K := by unfold jointEnvelope; omega

theorem usage_le_joint (s K : ℕ) : BinaryNestedProfileMeasured.envelope s K ≤ jointEnvelope s K := by unfold jointEnvelope; omega

macro "unfold_measured_nested_profile" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryNestedProfileMeasured.workEnvelope,BinaryNestedProfileMeasured.envelope,
    BinaryNestedProfileMeasured.orderedPrice,BinaryNestedProfileMeasured.orderedEnvelope,
    BinaryNestedThirdProfileMeasured.workEnvelope,BinaryNestedThirdProfileMeasured.envelope,BinaryNestedThirdProfileMeasured.mixtureWidth,
    BinaryNestedResidualMeasured.workEnvelope,BinaryNestedResidualMeasured.envelope,
    BinaryNestedResidualMeasured.environmentPrice,BinaryNestedResidualMeasured.environmentEnvelope,
    BinaryNestedResidualDescriptorMeasured.workEnvelope,BinaryNestedResidualDescriptorMeasured.envelope,
    BinaryNestedResidualDescriptorMeasured.arrayPrice,BinaryNestedResidualDescriptorMeasured.arrayEnvelope,
    BinaryNestedResidualDescriptorMeasured.expressionWork,BinaryNestedResidualDescriptorMeasured.expressionEnvelope,
    BinaryNestedResidualDescriptorLifetime.expressionEnvelope,
    BinaryNestedControlMeasured.workEnvelope,BinaryNestedControlMeasured.envelope,
    BinaryNestedControlMeasured.classifyPrice,BinaryNestedControlMeasured.classifyEnvelope,
    BinaryNestedControlMeasured.interiorPrice,BinaryNestedControlMeasured.interiorEnvelope,
    BinaryNestedBoundaryMeasured.workEnvelope,BinaryNestedBoundaryMeasured.envelope,
    BinaryNestedBoundaryMeasured.childPrice,BinaryNestedBoundaryMeasured.childEnvelope,
    BinaryNestedOrderMeasured.workEnvelope,BinaryNestedOrderLifetime.orderEnvelope,
    BinaryNestedRegimeMeasured.workEnvelope,BinaryNestedRegimeMeasured.widthEnvelope,BinaryNestedRegimeLifetime.envelope,
    BinarySmallUniformSplitMeasured.opcodePrice]
  <;> unfold_measured_nested_second)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth) := by
  unfold_measured_nested_profile
  resource_polynomial

theorem joint_mono {s K t N : ℕ} (hs : s ≤ t) (hk : K ≤ N) : jointEnvelope s K ≤ jointEnvelope t N := by
  unfold_measured_nested_profile
  unfold expressionHeightBudget
  gcongr

theorem joint_polynomial : ∃ C d : ℕ,∀ s K,jointEnvelope s K ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s K
  let T := s+K
  have hm : jointEnvelope s K ≤ jointEnvelope T T := joint_mono (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_bounds : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (hC : input.Canonical)
    (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K),
    (BinaryNestedProfileMeasured.profile input K bits).2 ≤ C*(s+K+2)^d ∧ usage (BinaryNestedProfileMeasured.profile input K bits).1.2 ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro input hC s hs hH K bits
  have h := BinaryNestedProfileMeasured.profile_bounds input hC s hs hH K bits
  have hb := hBound s K
  exact ⟨h.1.trans ((work_le_joint _ _).trans hb),h.2.trans ((usage_le_joint _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (hC : input.Canonical)
    (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryNestedProfileMeasured.profile input K bits).1.2 steps ≤ borrowed+C*(s+K+2)^d ∧
      framePeak ((BinaryNestedProfileMeasured.profile input K bits).1.2.take steps) ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro input hC s hs hH K bits borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound input hC s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedProfileMeasuredPolynomial
