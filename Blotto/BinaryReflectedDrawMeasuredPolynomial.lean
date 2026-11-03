import Blotto.BinaryReflectedDrawMeasured
import Blotto.BinaryReflectedProfileMeasuredPolynomial
import Blotto.BinaryWordDrawMeasuredPolynomial

/-! Original reflected fields and incoming scalar/choice parameters bound the
complete measured reflected draw's source work and every-prefix usage. The
existing profile polynomial combines with measured selection/emission prices;
native machine and whole-sampler adoption obligations remain separate. -/
namespace Blotto.BinaryReflectedDrawMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3500000

def suffixEnvelope (s K i cap : ℕ) : ℕ :=
  BinaryReflectedTableDrawMeasured.workEnvelope (expressionHeightBudget (max s (K+2)) 68) K i cap+
  BinaryReflectedTableDrawMeasured.envelope (expressionHeightBudget (max s (K+2)) 68) K i cap

def jointEnvelope (s K i cap : ℕ) : ℕ := BinaryReflectedProfileMeasuredPolynomial.jointEnvelope s i cap K+suffixEnvelope s K i cap+140000

theorem joined_le_joint (s K i cap : ℕ) : BinaryReflectedDrawMeasured.workEnvelope s K i cap+BinaryReflectedDrawMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  simp only [jointEnvelope,suffixEnvelope,BinaryReflectedDrawMeasured.workEnvelope,BinaryReflectedDrawMeasured.envelope,
    BinaryReflectedDrawMeasured.afterPrice,BinaryReflectedDrawMeasured.afterEnvelope,
    BinaryReflectedTerminalFactoryMeasured.workEnvelope,BinaryReflectedTerminalFactoryMeasured.envelope,
    BinaryReflectedProfileMeasuredPolynomial.jointEnvelope,BinaryReflectedProfilePrefixMeasured.workEnvelope,BinaryReflectedProfilePrefixMeasured.envelope,
    BinaryReflectedTerminalPrefixMeasured.workEnvelope,BinaryReflectedTerminalPrefixMeasured.envelope,BinaryReflectedTerminalPrefixMeasured.widthEnvelope]
  omega

theorem work_le_joint (s K i cap : ℕ) : BinaryReflectedDrawMeasured.workEnvelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

theorem usage_le_joint (s K i cap : ℕ) : BinaryReflectedDrawMeasured.envelope s K i cap ≤ jointEnvelope s K i cap := by
  have h := joined_le_joint s K i cap; omega

macro "unfold_measured_reflected_table_draw" : tactic => `(tactic|
  simp only [suffixEnvelope,BinaryReflectedTableDrawMeasured.workEnvelope,BinaryReflectedTableDrawMeasured.envelope,
    BinaryReflectedEmissionMeasured.workEnvelope,BinaryReflectedEmissionMeasured.envelope,
    BinaryReflectedEmissionMeasured.reflectPrice,BinaryReflectedEmissionMeasured.reflectEnvelope,
    BinaryReflectedEmissionMeasured.widthEnvelope,BinaryQuadraticPointOutputLifetime.rowWidth,
    BinaryReflectedSystemMeasured.opcodePrice,BinaryWordSegmentMeasured.selectionPrice,BinaryWordSegmentMeasured.sourceStepPrice,
    BinaryPhysicalPointMeasured.price,BinaryTapePointLifetime.bound]
  <;> unfold_word_terminal_envelope)

theorem suffix_diagonal : NaturalPolynomialEnvelope inputSize (fun p => suffixEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_reflected_table_draw
  resource_polynomial

theorem suffix_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    suffixEnvelope s K i cap ≤ suffixEnvelope t T I B := by
  unfold_measured_reflected_table_draw
  unfold expressionHeightBudget
  gcongr

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth) :=
  NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add BinaryReflectedProfileMeasuredPolynomial.diagonal_polynomial suffix_diagonal)
    (NaturalPolynomialEnvelope.constant inputSize 140000)

theorem joint_mono {s K i cap t T I B : ℕ} (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope s K i cap ≤ jointEnvelope t T I B := by
  have hPrefix := BinaryReflectedProfileMeasuredPolynomial.joint_mono hs hi hb hk
  have hSuffix := suffix_mono hs hk hi hb
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
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryReflectedSerialRun.Admissible input) (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).2 ≤ C*(s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).1.2 ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have h := BinaryReflectedDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have hb := hBound s K store.width store.cap.value
  exact ⟨h.1.trans ((work_le_joint _ _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryReflectedSerialRun.Admissible input) (s : ℕ),2 ≤ s → source.FieldsHeight s →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+C*(s+K+store.width+store.cap.value+2)^d ∧
      framePeak ((BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ C*(s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro store input source hC hR hCase hAd s hs hH K outer scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store input source hC hR hCase hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryReflectedDrawMeasuredPolynomial
