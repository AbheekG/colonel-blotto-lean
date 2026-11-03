import Blotto.GeneralPaperMeasuredUnequalStorageFrame

/-! Sharp rates for the complete measured unequal caller. Input owners
remain additive and saved time counters contribute only logarithms. -/
namespace Blotto.GeneralPaperMeasuredUnequalStorageRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperUniformResourceGrowth
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperMeasuredUnequalStorageFrame
open GeneralPaperNativeWorkingResourceRates (rate rate_positive)
open GeneralPaperNativeResourceReferenceGrowth (reserve)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem initializer_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    Bound (fun p => GeneralPaperMixedInitializerPhases.profile model (cal.word p) K
      (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)))
      (fun p => ledger p + 1) (logarithm model) := by
  obtain ⟨A, e, hA⟩ := GeneralPaperMixedInitializerCalibration.profile_rate model ⟨C, d, hg⟩ K
  refine ⟨2 * A * 2 ^ e, e, fun p => ?_⟩
  let input := GeneralPaperMeasuredReferenceGrowth.original p
  let ep := GeneralPaperOriginalGameInput.equalInput model input
  have hw : cal.word p = GeneralPaperEqualInputDomain.word K ep := congrFun hWord p
  have hLog : GeneralPaperEqualInputDomain.logarithm ep ≤ 2 * logarithm model p :=
    GeneralPaperOriginalReferenceComparison.measured_log_le model input p.budget_valid.2
  have hLedger : GeneralPaperEqualInputDomain.ledger ep ≤ 2 * (ledger p + 1) :=
    (GeneralPaperOriginalReferenceComparison.ledger_bounds model input p.budget_valid.2).2.2
  calc
    _ = GeneralPaperMixedInitializerPhases.profile model (GeneralPaperEqualInputDomain.word K ep) K ep := by
      change GeneralPaperMixedInitializerPhases.profile model (cal.word p) K ep = _
      rw [hw]
    _ ≤ A * GeneralPaperEqualInputDomain.ledger ep * (GeneralPaperEqualInputDomain.logarithm ep) ^ e := hA ep
    _ ≤ A * (2 * (ledger p + 1)) * (2 * logarithm model p) ^ e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left A hLedger) (Nat.pow_le_pow_left hLog e)
    _ = _ := by rw [mul_pow]; ring

theorem frame_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    Bound (frameProfile model C d cal K) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hi := rate_mono (initializer_rate hg cal K hWord)
    (fun p => show ledger p + 1 ≤ rate model p by unfold rate; omega)
  have hc := at_positive_rate (control_profile_polylog hg cal K hK) hR
  unfold frameProfile
  fun_prop

noncomputable def profile (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d)
    (K : ℕ) (p : Problem) : ℕ := frameProfile model C d cal K p + reserve model C d (cal.word p) p

theorem profile_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    Bound (profile model C d cal K) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hf := frame_rate hg cal K hK hWord
  have hr := GeneralPaperEnlargedReferenceSpace.reserve_rate hg cal
  unfold profile
  fun_prop

theorem profile_headline {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ A e : ℕ, ∀ p : Problem, GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1 →
      (profile model C d cal K p : ℚ) ≤
        (A : ℚ) * GeneralPaperNativeWorkingSpaceHeadline.spaceScale p *
          (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ e := by
  obtain ⟨A, e, hA⟩ := profile_rate hg cal K hK hWord
  refine ⟨A * 810448 * 4 ^ e, e, fun p hOne => ?_⟩
  have hRate := GeneralPaperNativeWorkingSpaceHeadline.structural_scale model p hOne
  have hLog := GeneralPaperNativeWorkingSpaceHeadline.log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (profile model C d cal K p : ℚ) ≤
      (A : ℚ) * (rate model p : ℚ) *
        ((4 : ℚ) * (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ)) ^ e := by exact_mod_cast hNat
  calc
    _ ≤ _ := hCast
    _ ≤ (A : ℚ) * (810448 * GeneralPaperNativeWorkingSpaceHeadline.spaceScale p) *
        ((4 : ℚ) * (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ)) ^ e := by gcongr
    _ = _ := by push_cast; rw [mul_pow]; ring

end Blotto.GeneralPaperMeasuredUnequalStorageRates
