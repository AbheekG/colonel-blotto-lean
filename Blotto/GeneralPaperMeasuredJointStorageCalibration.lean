import Blotto.GeneralPaperMeasuredEqualCapacityGrowth

/-! One fixed coefficient simultaneously covers both complete measured
branch envelopes, all enclosing owners and the unequal source floor. -/
namespace Blotto.GeneralPaperMeasuredJointStorageCalibration
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperMeasuredUnequalStorageCalibration (nativeEnvelope)
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

theorem joint_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : GeneralPaperOriginalGameInput.Input,
      let ep := GeneralPaperOriginalGameInput.equalInput model p
      let W := word K ep
      GeneralPaperMeasuredEqualDispatchStorage.envelope model W K ep + nativeEnvelope model C d W K p < 2 ^ W ∧
      ∀ h : p.budget < 1, GeneralPaperNativeResourceReferenceGrowth.word model C d
        (GeneralPaperOriginalGameInput.unequalInput p h) ≤ W := by
  obtain ⟨J, hJ⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  obtain ⟨CE, hE⟩ := GeneralPaperMeasuredEqualCapacityGrowth.uniform_word_growth model ⟨C, d, hg⟩
  obtain ⟨CN, hN⟩ := GeneralPaperMeasuredUnequalStorageCalibration.native_growth hg
  let L := fun p : GeneralPaperOriginalGameInput.Input => logarithm (GeneralPaperOriginalGameInput.equalInput model p)
  let lower := 8 * J
  let P := fun (W K : ℕ) (p : GeneralPaperOriginalGameInput.Input) =>
    GeneralPaperMeasuredEqualDispatchStorage.envelope model W K (GeneralPaperOriginalGameInput.equalInput model p) +
      nativeEnvelope model C d W K p + 2 ^ (lower * L p)
  have hGrowth : ∃ D : ℕ, ∀ (p : GeneralPaperOriginalGameInput.Input) (W K : ℕ),
      binaryWordWidth (P W K p) ≤ D * (L p + binaryWordWidth W + binaryWordWidth K) := by
    refine ⟨CE + CN + lower + 1, fun p W K => ?_⟩
    have he := hE (GeneralPaperOriginalGameInput.equalInput model p) W K
    have hn := hN p W K
    have hl : 1 ≤ L p := logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)
    have ht : binaryWordWidth (2 ^ (lower * L p)) ≤
        (lower + 1) * (L p + binaryWordWidth W + binaryWordWidth K) := by
      simp only [binaryWordWidth, Nat.log2_two_pow]
      nlinarith only [hl, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]
    have h0 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperMeasuredEqualDispatchStorage.envelope model W K (GeneralPaperOriginalGameInput.equalInput model p))
      (nativeEnvelope model C d W K p)
    have h1 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperMeasuredEqualDispatchStorage.envelope model W K (GeneralPaperOriginalGameInput.equalInput model p) +
        nativeEnvelope model C d W K p) (2 ^ (lower * L p))
    exact (h1.trans (Nat.add_le_add_right h0 _)).trans
      ((Nat.add_le_add (Nat.add_le_add he hn) ht).trans_eq (by dsimp only [L]; ring))
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

def Safe (model : RationalCostModel) (C d K : ℕ) : Prop :=
  ∀ p : GeneralPaperOriginalGameInput.Input,
    let ep := GeneralPaperOriginalGameInput.equalInput model p
    let W := word K ep
    GeneralPaperMeasuredEqualDispatchStorage.envelope model W K ep + nativeEnvelope model C d W K p < 2 ^ W

theorem calibrated_reference {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧ Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K := by
  obtain ⟨K, hK, hSafe⟩ := joint_capacity hg
  let cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d :=
    ⟨GeneralPaperMeasuredReferenceGrowth.word model K, GeneralPaperMeasuredReferenceGrowth.positive model K hK,
      GeneralPaperMeasuredReferenceGrowth.word_tight model K,
      fun p => (hSafe (GeneralPaperMeasuredReferenceGrowth.original p)).2 p.budget_valid.2⟩
  refine ⟨K, hK, cal, rfl, fun p => (hSafe p).1, fun p => ?_⟩
  have hs := (hSafe p).1
  dsimp only at hs ⊢
  unfold GeneralPaperMeasuredEqualDispatchStorage.envelope at hs
  omega

end Blotto.GeneralPaperMeasuredJointStorageCalibration
