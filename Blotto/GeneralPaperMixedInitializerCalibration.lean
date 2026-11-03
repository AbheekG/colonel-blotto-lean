import Blotto.GeneralPaperMixedInitializerPhases

/-! Mixed-width initialization retains its input-linear space rate and
admits one global coefficient with equal capacity and the unequal floor. -/
namespace Blotto.GeneralPaperMixedInitializerCalibration
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperMixedInitializerPhases (profile)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hR : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hOld := GeneralPaperEqualInputInitializerCapacity.profile_rate model hFast K
  have hWord := rate_mono (polylog_of_tight (word_tight K model)) hR
  unfold profile
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (profile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨C, hC⟩ := GeneralPaperEqualInputInitializerCapacity.uniform_word_growth model hFast
  refine ⟨C + 3, fun p W K => ?_⟩
  have ho := hC p W K
  have hm := binaryWordWidth_mul 2 W
  rw [show binaryWordWidth 2 = 2 by decide] at hm
  have ha := GeneralPaperReferenceScaling.word_add
    (GeneralPaperEqualInputInitializerLifetime.profile model W K p) (2 * W)
  have hL := logarithm_positive p
  change binaryWordWidth (GeneralPaperEqualInputInitializerLifetime.profile model W K p + 2 * W) ≤ _
  rw [Nat.add_mul]
  omega

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input model, profile model (word K p) K p < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (profile model) logarithm logarithm_positive
    (uniform_word_growth model hFast)

theorem joint_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : GeneralPaperOriginalGameInput.Input,
      let ep := GeneralPaperOriginalGameInput.equalInput model p
      GeneralPaperStoredPreparationUniformCapacity.envelope model K ep + profile model (word K ep) K ep <
        2 ^ word K ep ∧ ∀ h : p.budget < 1,
      GeneralPaperNativeResourceReferenceGrowth.word model C d (GeneralPaperOriginalGameInput.unequalInput p h) ≤ word K ep := by
  obtain ⟨J, hJ⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  obtain ⟨CE, hE⟩ := GeneralPaperStoredPreparationUniformCapacity.envelope_small model ⟨C, d, hg⟩
  obtain ⟨CP, hProfile⟩ := uniform_word_growth model ⟨C, d, hg⟩
  let L := fun p : GeneralPaperOriginalGameInput.Input => logarithm (GeneralPaperOriginalGameInput.equalInput model p)
  let lower := 8 * J
  let P := fun (W K : ℕ) (p : GeneralPaperOriginalGameInput.Input) =>
    GeneralPaperStoredPreparationUniformCapacity.envelope model K (GeneralPaperOriginalGameInput.equalInput model p) +
      profile model W K (GeneralPaperOriginalGameInput.equalInput model p) + 2 ^ (lower * L p)
  have hGrowth : ∃ D : ℕ, ∀ (p : GeneralPaperOriginalGameInput.Input) (W K : ℕ),
      binaryWordWidth (P W K p) ≤ D * (L p + binaryWordWidth W + binaryWordWidth K) := by
    refine ⟨CE + CP + lower + 1, fun p W K => ?_⟩
    let ep := GeneralPaperOriginalGameInput.equalInput model p
    have he := hE ⟨ep, W, K⟩
    change binaryWordWidth (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep) ≤
      CE * (L p + binaryWordWidth W + binaryWordWidth K) at he
    have hp := hProfile ep W K
    have hL : 1 ≤ L p := logarithm_positive ep
    have ht : binaryWordWidth (2 ^ (lower * L p)) ≤
        (lower + 1) * (L p + binaryWordWidth W + binaryWordWidth K) := by
      simp only [binaryWordWidth, Nat.log2_two_pow]
      nlinarith only [hL, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]
    have h0 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep) (profile model W K ep)
    have h1 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep + profile model W K ep) (2 ^ (lower * L p))
    exact (h1.trans (Nat.add_le_add_right h0 _)).trans
      ((Nat.add_le_add (Nat.add_le_add he hp) ht).trans_eq (by dsimp only [L, ep]; ring))
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperSelfReferenceCapacity.uniform_capacity P L
    (fun p => logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)) hGrowth
  refine ⟨K, hK, fun p => ?_⟩
  have hs := hSafe p
  dsimp only [P] at hs
  have hPositive : 0 < (2 : ℕ) ^ (lower * L p) := by positivity
  have hTail : 2 ^ (lower * L p) < 2 ^ (K * L p) := by omega
  have hFloor : lower * L p < K * L p := by
    by_contra hn
    have hm := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
    omega
  refine ⟨by change _ < 2 ^ (K * L p); exact lt_of_le_of_lt (Nat.le_add_right _ _) hs, fun h => ?_⟩
  calc
    _ ≤ J * GeneralPaperNativeResourceDomain.logarithm model (GeneralPaperOriginalGameInput.unequalInput p h) := hJ _
    _ ≤ J * (8 * L p) := Nat.mul_le_mul_left J (GeneralPaperOriginalReferenceComparison.native_log_le model p h)
    _ = lower * L p := by dsimp only [lower]; ring
    _ ≤ K * L p := hFloor.le

theorem original_input_contract {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : GeneralPaperOriginalGameInput.Input,
      GeneralPaperOriginalGameInput.epsilon p < 1 →
      ∃ output, (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
        GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
        let S := (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2
        (∀ phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n,
          GeneralPaperMixedInitializerPhases.window model S 1 K (GeneralPaperOriginalGameInput.equalInput model p) phase < 2 ^ S) ∧
        GeneralPaperStoredPreparationUniformCapacity.envelope model K (GeneralPaperOriginalGameInput.equalInput model p) < 2 ^ S ∧
        ∀ h : p.budget < 1, GeneralPaperNativeResourceReferenceGrowth.word model C d
          (GeneralPaperOriginalGameInput.unequalInput p h) ≤ S := by
  obtain ⟨K, hK, hSafe⟩ := joint_capacity hg
  refine ⟨K, hK, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hLaw, hPointwise⟩ := GeneralPaperMeasuredBitDispatch.original_game_contract model K p hOne
  refine ⟨output, hReturn, hLaw, hPointwise, ?_⟩
  dsimp only
  rw [GeneralPaperOriginalMeasuredReference.word]
  have hs := hSafe p
  dsimp only at hs
  have hp : profile model (word K (GeneralPaperOriginalGameInput.equalInput model p)) K
      (GeneralPaperOriginalGameInput.equalInput model p) < 2 ^ word K (GeneralPaperOriginalGameInput.equalInput model p) := by omega
  refine ⟨fun phase => (GeneralPaperMixedInitializerPhases.all_phases model _ 1 K
    (Nat.mul_le_mul hK (logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)))
    (GeneralPaperOriginalGameInput.equalInput model p) phase).trans_lt hp, ?_, hs.2⟩
  change GeneralPaperStoredPreparationUniformCapacity.envelope model K (GeneralPaperOriginalGameInput.equalInput model p) <
    2 ^ word K (GeneralPaperOriginalGameInput.equalInput model p)
  omega

theorem calibrated_reference {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      ∀ p : GeneralPaperOriginalGameInput.Input,
        let ep := GeneralPaperOriginalGameInput.equalInput model p
        GeneralPaperStoredPreparationUniformCapacity.envelope model K ep + profile model (word K ep) K ep < 2 ^ word K ep := by
  obtain ⟨K, hK, hSafe⟩ := joint_capacity hg
  let cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d :=
    ⟨GeneralPaperMeasuredReferenceGrowth.word model K, GeneralPaperMeasuredReferenceGrowth.positive model K hK,
      GeneralPaperMeasuredReferenceGrowth.word_tight model K,
      fun p => (hSafe (GeneralPaperMeasuredReferenceGrowth.original p)).2 p.budget_valid.2⟩
  exact ⟨K, hK, cal, rfl, fun p => (hSafe p).1⟩

end Blotto.GeneralPaperMixedInitializerCalibration
