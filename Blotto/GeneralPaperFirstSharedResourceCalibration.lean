import Blotto.GeneralPaperFirstSharedBitCalibration
import Blotto.GeneralPaperFirstEqualCapacityGrowth

/-! One fixed computed coefficient covers the corrected equal program and
all unchanged unequal preparation contracts. Prior envelopes are used only
as erased upper reserves to preserve their native capacity guarantees; the
selected equal program executes the corrected c=256 direct installer. -/
namespace Blotto.GeneralPaperFirstSharedResourceCalibration
open GeneralPaperEqualInputDomain
open GeneralPaperMeasuredUnequalStorageCalibration (nativeEnvelope)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def EqualSafe (model : RationalCostModel) (K : ℕ) : Prop :=
  ∀ p : GeneralPaperOriginalGameInput.Input,
    GeneralPaperFirstEqualDispatchStorage.envelope model (word K (GeneralPaperOriginalGameInput.equalInput model p)) K (GeneralPaperOriginalGameInput.equalInput model p)<
      2^word K (GeneralPaperOriginalGameInput.equalInput model p)

theorem joint_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ,1≤K ∧ EqualSafe model K ∧ GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      ∀ p : GeneralPaperOriginalGameInput.Input,∀ h : p.budget<1,
        GeneralPaperNativeResourceReferenceGrowth.word model C d (GeneralPaperOriginalGameInput.unequalInput p h) ≤
          word K (GeneralPaperOriginalGameInput.equalInput model p) := by
  obtain ⟨J,hJ⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  obtain ⟨CF,hF⟩ := GeneralPaperFirstEqualCapacityGrowth.uniform_word_growth model ⟨C,d,hg⟩
  obtain ⟨CE,hE⟩ := GeneralPaperMeasuredEqualCapacityGrowth.uniform_word_growth model ⟨C,d,hg⟩
  obtain ⟨CN,hN⟩ := GeneralPaperMeasuredUnequalStorageCalibration.native_growth hg
  let L := fun p : GeneralPaperOriginalGameInput.Input => logarithm (GeneralPaperOriginalGameInput.equalInput model p)
  let lower := 8*J
  let P := fun (W K : ℕ) (p : GeneralPaperOriginalGameInput.Input) =>
    GeneralPaperFirstEqualDispatchStorage.envelope model W K (GeneralPaperOriginalGameInput.equalInput model p)+
      GeneralPaperMeasuredEqualDispatchStorage.envelope model W K (GeneralPaperOriginalGameInput.equalInput model p)+
      nativeEnvelope model C d W K p+2^(lower*L p)
  have hGrowth : ∃ D : ℕ,∀ (p : GeneralPaperOriginalGameInput.Input) (W K : ℕ),
      binaryWordWidth (P W K p) ≤ D*(L p+binaryWordWidth W+binaryWordWidth K) := by
    refine ⟨CF+CE+CN+lower+1,fun p W K => ?_⟩
    let ep := GeneralPaperOriginalGameInput.equalInput model p
    have hf := hF ep W K
    have he := hE ep W K
    have hn := hN p W K
    have hl : 1≤L p := logarithm_positive ep
    have ht : binaryWordWidth (2^(lower*L p)) ≤
        (lower+1)*(L p+binaryWordWidth W+binaryWordWidth K) := by
      simp only [binaryWordWidth,Nat.log2_two_pow]
      nlinarith only [hl,Nat.zero_le (binaryWordWidth W),Nat.zero_le (binaryWordWidth K)]
    have h0 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperFirstEqualDispatchStorage.envelope model W K ep) (GeneralPaperMeasuredEqualDispatchStorage.envelope model W K ep)
    have h1 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperFirstEqualDispatchStorage.envelope model W K ep+GeneralPaperMeasuredEqualDispatchStorage.envelope model W K ep)
      (nativeEnvelope model C d W K p)
    have h2 := GeneralPaperReferenceScaling.word_add
      (GeneralPaperFirstEqualDispatchStorage.envelope model W K ep+GeneralPaperMeasuredEqualDispatchStorage.envelope model W K ep+
        nativeEnvelope model C d W K p) (2^(lower*L p))
    exact (h2.trans (Nat.add_le_add_right (h1.trans (Nat.add_le_add_right h0 _)) _)).trans
      ((Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf he) hn) ht).trans_eq (by
        dsimp only [L,ep,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]
        ring))
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperSelfReferenceCapacity.uniform_capacity P L
    (fun p => logarithm_positive (GeneralPaperOriginalGameInput.equalInput model p)) hGrowth
  refine ⟨K,hK,fun p => ?_,fun p => ?_,fun p h => ?_⟩
  · have hs := hSafe p
    have hPositive := Nat.two_pow_pos (lower*L p)
    dsimp only [P,L,word] at hs hPositive ⊢
    omega
  · have hs := hSafe p
    have hPositive := Nat.two_pow_pos (lower*L p)
    dsimp only [P,L,word] at hs hPositive ⊢
    omega
  · have hs := hSafe p
    dsimp only [P] at hs
    have hTail : 2^(lower*L p)<2^(K*L p) := by omega
    have hFloor : lower*L p<K*L p := by
      by_contra hn
      have hm := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (Nat.le_of_not_gt hn)
      omega
    calc
      _ ≤ J*GeneralPaperNativeResourceDomain.logarithm model (GeneralPaperOriginalGameInput.unequalInput p h) := hJ _
      _ ≤ J*(8*L p) := Nat.mul_le_mul_left J (GeneralPaperOriginalReferenceComparison.native_log_le model p h)
      _ = lower*L p := by dsimp only [lower]; ring
      _ ≤ K*L p := hFloor.le

theorem calibrated_reference {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ,1≤K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word=GeneralPaperMeasuredReferenceGrowth.word model K ∧ EqualSafe model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧ GeneralPaperMeasuredUnequalFullContract.Safe model C d K := by
  obtain ⟨K,hK,hEqual,hSafe,hFloor⟩ := joint_capacity hg
  let cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d :=
    ⟨GeneralPaperMeasuredReferenceGrowth.word model K,GeneralPaperMeasuredReferenceGrowth.positive model K hK,
      GeneralPaperMeasuredReferenceGrowth.word_tight model K,
      fun p => hFloor (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2⟩
  refine ⟨K,hK,cal,rfl,hEqual,hSafe,fun p => ?_⟩
  have hs := hSafe p
  dsimp only at hs ⊢
  unfold GeneralPaperMeasuredEqualDispatchStorage.envelope at hs
  omega

end Blotto.GeneralPaperFirstSharedResourceCalibration
