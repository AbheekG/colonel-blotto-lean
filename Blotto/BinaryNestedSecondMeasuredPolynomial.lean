import Blotto.BinaryNestedSecondProfileMeasured
import Blotto.BinaryNestedControlMeasuredPolynomial

/-! The complete measured second interior producer has a uniform polynomial
source-work and retained-usage envelope in original field height and scalar
width. Native machine costs and the complete reflected dispatch remain. -/
namespace Blotto.BinaryNestedSecondMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3500000

def jointEnvelope (s K : ℕ) : ℕ := BinaryNestedSecondProfileMeasured.workEnvelope s K+BinaryNestedSecondProfileMeasured.envelope s K

theorem work_le_joint (s K : ℕ) : BinaryNestedSecondProfileMeasured.workEnvelope s K ≤ jointEnvelope s K := by unfold jointEnvelope; omega

theorem usage_le_joint (s K : ℕ) : BinaryNestedSecondProfileMeasured.envelope s K ≤ jointEnvelope s K := by unfold jointEnvelope; omega

macro "unfold_measured_nested_second" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryNestedSecondProfileMeasured.workEnvelope,BinaryNestedSecondProfileMeasured.envelope,
    BinaryNestedSecondProfileMeasured.mixtureWidth,
    BinaryNestedFamilyMeasured.workEnvelope,BinaryNestedFamilyMeasured.envelope,
    BinaryNestedFamilyMeasured.inputPrice,BinaryNestedFamilyMeasured.inputEnvelope,
    BinaryNestedSecondUniformMeasured.workEnvelope,BinaryNestedSecondUniformMeasured.envelope,
    BinaryNestedSecondUniformMeasured.inputPrice,BinaryNestedSecondUniformMeasured.inputEnvelope,
    BinaryNestedSecondUniformMeasured.shiftWidth,
    BinaryNestedBinaryAssemblyMeasured.workEnvelope,BinaryNestedBinaryAssemblyMeasured.envelope,
    BinaryNestedBinaryAssemblyMeasured.weightPrice,BinaryNestedBinaryAssemblyMeasured.weightEnvelope,
    BinaryReflectedSystemMeasured.opcodePrice,BinaryLifetimeUsage.opcodeEnvelope]
  <;> unfold_measured_nested_first)

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth) := by
  unfold_measured_nested_second
  resource_polynomial

theorem joint_mono {s K t N : ℕ} (hs : s ≤ t) (hk : K ≤ N) : jointEnvelope s K ≤ jointEnvelope t N := by
  unfold_measured_nested_second
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

theorem source_bounds : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical),parameters = BinaryNestedProfileCompiler.parameters input →
    ∀ (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K),
    (BinaryNestedSecondProfileMeasured.profile input parameters K bits).2 ≤ C*(s+K+2)^d ∧
      usage (BinaryNestedSecondProfileMeasured.profile input parameters K bits).1.2 ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro input parameters hC hParameters s hs hH K bits
  have h := BinaryNestedSecondProfileMeasured.profile_bounds input parameters hC hParameters s hs hH K bits
  have hb := hBound s K
  exact ⟨h.1.trans ((work_le_joint _ _).trans hb),h.2.trans ((usage_le_joint _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (input : BinaryNestedParameters.Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical),parameters = BinaryNestedProfileCompiler.parameters input →
    ∀ (s : ℕ),3 ≤ s → BinaryNestedParameterWork.InputHeight input s → ∀ (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryNestedSecondProfileMeasured.profile input parameters K bits).1.2 steps ≤ borrowed+C*(s+K+2)^d ∧
      framePeak ((BinaryNestedSecondProfileMeasured.profile input parameters K bits).1.2.take steps) ≤ C*(s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro input parameters hC hParameters s hs hH K bits borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound input parameters hC hParameters s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedSecondMeasuredPolynomial
