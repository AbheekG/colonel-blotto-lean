import Blotto.BinaryWordTerminalCompleteMeasured
import Blotto.BinaryFourMeasuredPolynomial
import Blotto.BinaryWordDrawMeasuredPolynomial

/-! Original terminal cache fields and seed/scalar parameters bound complete
measured terminal drawing and route emission uniformly by a polynomial. The
four-variable contribution composes its existing optional-draw bound, retaining
the complete caller's global fallback semantics and native-model boundary. -/
namespace Blotto.BinaryWordTerminalCompletePolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourcePolynomial BinaryCachedGroupInputHeight BinaryCachedThreeDescriptorWork
set_option autoImplicit false
set_option maxHeartbeats 4500000

def extraEnvelope (n s K i cap : ℕ) : ℕ :=
  BinaryWordGroupCompleteMeasured.uniformPrice n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformPrice n 3 s K i cap+
  BinaryWordGroupCompleteMeasured.mixedTwoPrice n s K i cap+
  BinaryWordGroupCompleteMeasured.uniformEnvelope n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformEnvelope n 3 s K i cap+
  BinaryWordGroupCompleteMeasured.mixedTwoEnvelope n s K i cap+
  BinaryGroupEmissionMeasured.mixedWorkEnvelope n 3 (BinaryWordGroupEmissionLifetime.groupHeight s K)+
  BinaryGroupEmissionMeasured.mixedEnvelope n 3 (BinaryWordGroupEmissionLifetime.groupHeight s K)+512

def jointEnvelope (n s K i cap : ℕ) : ℕ := BinaryFourMeasuredPolynomial.jointEnvelope s K i cap+extraEnvelope n s K i cap

theorem joined_le_joint (n s K i cap : ℕ) :
    BinaryWordTerminalCompleteMeasured.workEnvelope n s K i cap+BinaryWordTerminalCompleteMeasured.envelope n s K i cap ≤
      jointEnvelope n s K i cap := by
  have h := BinaryFourMeasuredPolynomial.joined_le_joint s K i cap
  simp only [jointEnvelope,extraEnvelope,BinaryWordTerminalCompleteMeasured.workEnvelope,BinaryWordTerminalCompleteMeasured.envelope,
    BinaryWordGroupCompleteMeasured.mixedThreePrice,BinaryWordGroupCompleteMeasured.mixedThreeEnvelope]
  omega

theorem work_le_joint (n s K i cap : ℕ) : BinaryWordTerminalCompleteMeasured.workEnvelope n s K i cap ≤ jointEnvelope n s K i cap := by
  have h := joined_le_joint n s K i cap; omega

theorem usage_le_joint (n s K i cap : ℕ) : BinaryWordTerminalCompleteMeasured.envelope n s K i cap ≤ jointEnvelope n s K i cap := by
  have h := joined_le_joint n s K i cap; omega

macro "unfold_measured_terminal_extra" : tactic => `(tactic|
  simp only [extraEnvelope,BinaryWordGroupCompleteMeasured.uniformPrice,BinaryWordGroupCompleteMeasured.uniformEnvelope,
    BinaryWordGroupCompleteMeasured.mixedTwoPrice,BinaryWordGroupCompleteMeasured.mixedTwoEnvelope,
    BinaryWordGroupDrawMeasured.uniformEnvelope,BinaryWordGroupDrawMeasured.mixedEnvelope,
    BinaryGroupEmissionMeasured.mixedWorkEnvelope,BinaryGroupEmissionMeasured.mixedEnvelope,
    BinaryGroupEmissionMeasured.workEnvelope,BinaryGroupEmissionMeasured.envelope,BinaryGroupEmissionMeasured.referenceEnvelope,
    BinaryWordGroupEmissionLifetime.groupHeight,BinaryLifetimeArrayMeasured.storageReserve]
  <;> unfold_measured_draw_work)

theorem extra_diagonal : NaturalPolynomialEnvelope inputSize
    (fun p => extraEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_measured_terminal_extra
  resource_polynomial

theorem extra_mono {n s K i cap N t T I B : ℕ} (hn : n ≤ N) (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    extraEnvelope n s K i cap ≤ extraEnvelope N t T I B := by
  unfold_measured_terminal_extra
  unfold expressionHeightBudget
  gcongr

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => jointEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) :=
  NaturalPolynomialEnvelope.add BinaryFourMeasuredPolynomial.diagonal_polynomial extra_diagonal

theorem joint_mono {n s K i cap N t T I B : ℕ} (hn : n ≤ N) (hs : s ≤ t) (hk : K ≤ T) (hi : i ≤ I) (hb : cap ≤ B) :
    jointEnvelope n s K i cap ≤ jointEnvelope N t T I B := by
  have hFour := BinaryFourMeasuredPolynomial.joint_mono hs hk hi hb
  have hExtra := extra_mono hn hs hk hi hb
  unfold jointEnvelope
  omega

theorem joint_polynomial : ∃ C d : ℕ,∀ n s K i cap,jointEnvelope n s K i cap ≤ C*(n+s+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro n s K i cap
  let T := n+s+K+i+cap
  have hm : jointEnvelope n s K i cap ≤ jointEnvelope T T T T T := joint_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
    (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hm.trans h

theorem source_bounds : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : BinaryCachedTerminalPreparation.Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ),3 ≤ s → UniformHeights prepared.uniform s →
    (∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s) →
    (∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1)) →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).2 ≤ C*(n+s+K+store.width+store.cap.value+2)^d ∧
      usage (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2 ≤ C*(n+s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro n store input prepared hC hAd s hs hU hM hR K outer scalar pc hp
  have h := BinaryWordTerminalCompleteMeasured.run_bounds store prepared hC hAd s hs hU hM hR K outer scalar pc hp
  have hb := hBound n s K store.width store.cap.value
  exact ⟨h.1.trans ((work_le_joint _ _ _ _ _).trans hb),h.2.trans ((usage_le_joint _ _ _ _ _).trans hb)⟩

theorem source_all_prefix : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : BinaryCachedTerminalPreparation.Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ),3 ≤ s → UniformHeights prepared.uniform s →
    (∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s) →
    (∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1)) →
    ∀ (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ),
    retainedHeap borrowed (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2 steps ≤
      borrowed+C*(n+s+K+store.width+store.cap.value+2)^d ∧
    framePeak ((BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2.take steps) ≤
      C*(n+s+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := source_bounds
  refine ⟨C,d,?_⟩
  intro n store input prepared hC hAd s hs hU hM hR K outer scalar pc hp borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store prepared hC hAd s hs hU hM hR K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryWordTerminalCompletePolynomial
