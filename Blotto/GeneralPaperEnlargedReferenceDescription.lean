import Blotto.GeneralPaperArbitraryPreparationDraw

/-! The paper compact-description power at any logarithmic preparation
word. Complete prepared and sampler footprints refer to the same return. -/
namespace Blotto.GeneralPaperEnlargedReferenceDescription
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive paperLog)
open GeneralPaperNativeReturnedDescriptionHeadline (descriptionScale paper_log_positive epsilon_scale_nonnegative description_scale_nonnegative)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem description_word_bound {model : RationalCostModel} {C d : ℕ} (cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d) :
    ∃ D : ℕ,∀ p : Problem,GeneralPaperDescriptionHeadline.epsilonWord (cal.word p) p.n (epsilon p)≤D*paperLog p := by
  obtain ⟨K,hK⟩ := cal.tight
  refine ⟨4*K+1,?_⟩
  intro p
  have hLog := GeneralPaperNativeWorkingSpaceHeadline.log_comparison model p
  have hWord := (hK p).trans (Nat.mul_le_mul_left K hLog)
  have hBase : GeneralPaperDescriptionHeadline.epsilonWord (cal.word p) p.n (epsilon p)≤cal.word p+paperLog p := by
    unfold GeneralPaperDescriptionHeadline.epsilonWord GeneralPaperNativeWorkingSpaceHeadline.paperLog
    omega
  nlinarith only [hBase,hWord]

theorem envelope_bound {model : RationalCostModel} {C d : ℕ} (cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d) :
    ∃ A : ℕ,∀ p : Problem,
      4*(ledger p:ℚ)+((2^90*10952:ℕ):ℚ)*GeneralPaperDescriptionHeadline.epsilonScale p.n (epsilon p)*
        (GeneralPaperDescriptionHeadline.epsilonWord (cal.word p) p.n (epsilon p):ℚ)^2≤
      (A:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 := by
  obtain ⟨D,hD⟩ := description_word_bound cal
  refine ⟨4+(2^90*10952)*D^2,?_⟩
  intro p
  have hS := epsilon_scale_nonnegative p
  have hScale := description_scale_nonnegative p
  have hSle : GeneralPaperDescriptionHeadline.epsilonScale p.n (epsilon p)≤descriptionScale p := by
    unfold descriptionScale
    exact le_add_of_nonneg_left (by positivity)
  have hLedger : (ledger p:ℚ)≤descriptionScale p := by
    unfold descriptionScale
    push_cast
    linarith only [hS]
  have hLog : (1:ℚ)≤(paperLog p:ℚ)^2 := by
    have h : (1:ℚ)≤(paperLog p:ℚ) := by exact_mod_cast paper_log_positive p
    nlinarith only [h]
  have hLedgerScaled : (ledger p:ℚ)≤descriptionScale p*(paperLog p:ℚ)^2 :=
    hLedger.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hLog hScale)
  have hWord : (GeneralPaperDescriptionHeadline.epsilonWord (cal.word p) p.n (epsilon p):ℚ)≤(D:ℚ)*(paperLog p:ℚ) := by
    exact_mod_cast hD p
  have hPow : (GeneralPaperDescriptionHeadline.epsilonWord (cal.word p) p.n (epsilon p):ℚ)^2≤((D:ℚ)*(paperLog p:ℚ))^2 := by gcongr
  have hProduct := mul_le_mul hSle hPow (by positivity) hScale
  have hProduct' := mul_le_mul_of_nonneg_left hProduct (by positivity : (0:ℚ)≤((2^90*10952:ℕ):ℚ))
  have hBase := mul_le_mul_of_nonneg_left hLedgerScaled (by norm_num : (0:ℚ)≤4)
  convert add_le_add hBase hProduct' using 1
  · ring
  · push_cast
    ring

theorem native_bit_return_description {model : RationalCostModel} {C d : ℕ} (cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d) :
    ∃ A : ℕ,∀ p : Problem,epsilon p<1 →
      let W := cal.word p
      let actual := (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
      let o := actual.raw.strategies.original.reduced
      let k := actual.raw.exponent
      let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
      ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
        actual.sampler=some sampler ∧
        (GeneralPaperClosedDescriptionStorage.footprint W sampler:ℚ)≤(A:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 ∧
        (GeneralPaperClosedDescriptionStorage.preparedFoot W actual:ℚ)≤(A:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 := by
  obtain ⟨A,hA⟩ := envelope_bound cal
  refine ⟨A,?_⟩
  intro p hOne
  let W := cal.word p
  obtain ⟨sampler,hSampler,hFoot,hPrepared⟩ := GeneralPaperDescriptionHeadline.epsilon_description model W W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid (ledger p) (source model p).hB
  exact ⟨sampler,hSampler,hFoot.trans (hA p),hPrepared.trans (hA p)⟩

end Blotto.GeneralPaperEnlargedReferenceDescription
