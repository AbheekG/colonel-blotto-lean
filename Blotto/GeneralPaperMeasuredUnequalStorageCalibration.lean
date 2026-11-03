import Blotto.GeneralPaperMeasuredUnequalCapacityGrowth

/-! One fixed coefficient covers complete unequal caller capacity as well
as the existing equal preparation and mixed initializer envelopes. -/
namespace Blotto.GeneralPaperMeasuredUnequalStorageCalibration
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

noncomputable def nativeEnvelope (model : RationalCostModel) (C d W K : ℕ)
    (p : GeneralPaperOriginalGameInput.Input) : ℕ :=
  if h : p.budget < 1 then GeneralPaperMeasuredUnequalCapacityEnvelope.envelope model C d W K
    (GeneralPaperOriginalGameInput.unequalInput p h) else 0

theorem native_growth {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ D : ℕ, ∀ (p : GeneralPaperOriginalGameInput.Input) (W K : ℕ),
      binaryWordWidth (nativeEnvelope model C d W K p) ≤
        D * (logarithm (GeneralPaperOriginalGameInput.equalInput model p) + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨B, hB⟩ := GeneralPaperMeasuredUnequalCapacityGrowth.uniform_word_growth hg
  refine ⟨8 * B + 1, fun p W K => ?_⟩
  dsimp only [nativeEnvelope]
  split_ifs with h
  ·
    have hb := hB (GeneralPaperOriginalGameInput.unequalInput p h) W K
    have hl := GeneralPaperOriginalReferenceComparison.native_log_le model p h
    change GeneralPaperNativeResourceDomain.logarithm model (GeneralPaperOriginalGameInput.unequalInput p h) ≤
      8 * logarithm (GeneralPaperOriginalGameInput.equalInput model p) at hl
    nlinarith only [hb, hl, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]
  ·
    have hl := logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)
    change 1 ≤ _
    nlinarith only [hl, Nat.zero_le B, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]

theorem joint_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : GeneralPaperOriginalGameInput.Input,
      let ep := GeneralPaperOriginalGameInput.equalInput model p
      let W := word K ep
      GeneralPaperStoredPreparationUniformCapacity.envelope model K ep +
        GeneralPaperMixedInitializerPhases.profile model W K ep + nativeEnvelope model C d W K p < 2 ^ W ∧
      ∀ h : p.budget < 1, GeneralPaperNativeResourceReferenceGrowth.word model C d
        (GeneralPaperOriginalGameInput.unequalInput p h) ≤ W := by
  obtain ⟨J, hJ⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  obtain ⟨CE, hE⟩ := GeneralPaperStoredPreparationUniformCapacity.envelope_small model ⟨C, d, hg⟩
  obtain ⟨CI, hI⟩ := GeneralPaperMixedInitializerCalibration.uniform_word_growth model ⟨C, d, hg⟩
  obtain ⟨CN, hN⟩ := native_growth hg
  let L := fun p : GeneralPaperOriginalGameInput.Input => logarithm (GeneralPaperOriginalGameInput.equalInput model p)
  let lower := 8 * J
  let P := fun (W K : ℕ) (p : GeneralPaperOriginalGameInput.Input) =>
    GeneralPaperStoredPreparationUniformCapacity.envelope model K (GeneralPaperOriginalGameInput.equalInput model p) +
      GeneralPaperMixedInitializerPhases.profile model W K (GeneralPaperOriginalGameInput.equalInput model p) +
      nativeEnvelope model C d W K p + 2 ^ (lower * L p)
  have hGrowth : ∃ D : ℕ, ∀ (p : GeneralPaperOriginalGameInput.Input) (W K : ℕ),
      binaryWordWidth (P W K p) ≤ D * (L p + binaryWordWidth W + binaryWordWidth K) := by
    refine ⟨CE + CI + CN + lower + 1, fun p W K => ?_⟩
    let ep := GeneralPaperOriginalGameInput.equalInput model p
    have he := hE ⟨ep, W, K⟩
    change binaryWordWidth (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep) ≤
      CE * (L p + binaryWordWidth W + binaryWordWidth K) at he
    have hi := hI ep W K
    have hn := hN p W K
    have hl : 1 ≤ L p := logarithm_positive ep
    have ht : binaryWordWidth (2 ^ (lower * L p)) ≤
        (lower + 1) * (L p + binaryWordWidth W + binaryWordWidth K) := by
      simp only [binaryWordWidth, Nat.log2_two_pow]
      nlinarith only [hl, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]
    have h0 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep)
      (GeneralPaperMixedInitializerPhases.profile model W K ep)
    have h1 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep + GeneralPaperMixedInitializerPhases.profile model W K ep)
      (nativeEnvelope model C d W K p)
    have h2 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperStoredPreparationUniformCapacity.envelope model K ep + GeneralPaperMixedInitializerPhases.profile model W K ep +
        nativeEnvelope model C d W K p) (2 ^ (lower * L p))
    exact (h2.trans (Nat.add_le_add_right (h1.trans (Nat.add_le_add_right h0 _)) _)).trans
      ((Nat.add_le_add (Nat.add_le_add (Nat.add_le_add he hi) hn) ht).trans_eq (by dsimp only [L, ep]; ring))
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperSelfReferenceCapacity.uniform_capacity P L
    (fun p => logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)) hGrowth
  refine ⟨K, hK, fun p => ?_⟩
  have hs := hSafe p
  dsimp only [P] at hs
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

end Blotto.GeneralPaperMeasuredUnequalStorageCalibration
