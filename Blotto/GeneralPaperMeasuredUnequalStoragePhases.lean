import Blotto.GeneralPaperMeasuredUnequalStorageRates

/-! Complete initializer/continuation/return phase family for the measured
unequal producer. The selected exponent below is an erased equality view,
not another executed accuracy scan. Outer owners coexist with child space. -/
namespace Blotto.GeneralPaperMeasuredUnequalStoragePhases
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperMeasuredUnequalStorageFrame (initial child frame)
open GeneralPaperClosedParsedStorage (SourceCursor DescriptionCursor)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def word (model : RationalCostModel) (K : ℕ) (p : Problem) : ℕ := (initial model K p).1.2

def selected (model : RationalCostModel) (K : ℕ) (p : Problem) : ℕ :=
  (GeneralPaperBinaryAccuracy.prepare (fun w => w) (word model K p) p.words).1

theorem selected_actual (model : RationalCostModel) (K : ℕ) (p : Problem) :
    (initial model K p).1.1.exponent = selected model K p := by
  exact (GeneralPaperBinaryAccuracy.prepare_data id 1 p.words).trans
    (GeneralPaperBinaryAccuracy.prepare_data (fun w => w) (word model K p) p.words).symm

inductive Phase (model : RationalCostModel) (K : ℕ) (p : Problem)
  | initialization (phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n)
  | native (source : SourceCursor model (word model K p) (selected model K p) p.values p.selector p.correct)
      (description : DescriptionCursor model (word model K p) (selected model K p) p.values p.selector p.correct)
  | returned

noncomputable def window (model : RationalCostModel) (K : ℕ) (p : Problem) : Phase model K p → ℕ
  | .initialization phase =>
      GeneralPaperMixedInitializerPhases.window model (word model K p) 1 K
        (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) phase +
      GeneralPaperEncodedScalarStorage.fields (word model K p)
        (GeneralPaperMeasuredUnequalStorageFrame.values model K p) + 384 * word model K p
  | .native source description =>
      GeneralPaperClosedParsedStorage.window model (word model K p) (selected model K p)
        p.values p.selector p.correct p.budget p.budget_valid source description + frame model K p
  | .returned => GeneralPaperClosedDescriptionStorage.preparedFoot (word model K p)
      (GeneralPaperMeasuredUnequalSampling.actual model K p) + frame model K p

theorem word_eq {model : RationalCostModel} {C d : ℕ} (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    word model K p = cal.word p :=
  (GeneralPaperOriginalMeasuredReference.word model 1 K _).trans (congrFun hWord p).symm

theorem returned_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    GeneralPaperClosedDescriptionStorage.preparedFoot (cal.word p)
      (GeneralPaperMeasuredUnequalSampling.actual model K p) ≤
        GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p := by
  rw [GeneralPaperMeasuredUnequalSampling.data, ← congrFun hWord p]
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1
  let original := (GeneralPaperOriginalSourceValuePreparation.run true model (cal.word p) k p.values p.selector p.correct).1
  exact GeneralPaperEnlargedReferenceSpace.returned_covered hg cal p
    (GeneralPaperNativeSourceTimeRates.initialCursor original.reduced.m k original.Qv)
    ⟨0, Nat.zero_le _, 0, Nat.zero_le _, 0, Nat.zero_le _, 0, 0, none⟩

theorem all_phases {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) (phase : Phase model K p) :
    window model K p phase ≤ GeneralPaperMeasuredUnequalStorageRates.profile model C d cal K p := by
  have hw := word_eq cal K hWord p
  have hf := GeneralPaperMeasuredUnequalStorageFrame.frame_bound hg cal K hWord p
  cases phase with
  | initialization phase =>
    have hi := GeneralPaperMixedInitializerPhases.all_phases model (cal.word p) 1 K (cal.positive p)
      (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) phase
    have hc := GeneralPaperMeasuredUnequalStorageFrame.controls_bound hg cal K hWord p
    dsimp only [window]
    rw [hw]
    unfold GeneralPaperMeasuredUnequalStorageRates.profile GeneralPaperMeasuredUnequalStorageFrame.frameProfile
    omega
  | native source description =>
    have hn : ∀ (source : SourceCursor model (word model K p) (selected model K p) p.values p.selector p.correct)
        (description : DescriptionCursor model (word model K p) (selected model K p) p.values p.selector p.correct),
        GeneralPaperClosedParsedStorage.window model (word model K p) (selected model K p)
          p.values p.selector p.correct p.budget p.budget_valid source description ≤
            GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p := by
      dsimp only [selected]
      rw [hw]
      exact GeneralPaperEnlargedReferenceSpace.parsed_window hg cal p
    have hs := hn source description
    dsimp only [window, GeneralPaperMeasuredUnequalStorageRates.profile]
    omega
  | returned =>
    have hr := returned_bound hg cal K hWord p
    dsimp only [window]
    rw [hw]
    unfold GeneralPaperMeasuredUnequalStorageRates.profile
    omega

theorem headline {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ A e : ℕ, ∀ p : Problem, GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1 →
      ∀ phase : Phase model K p, (window model K p phase : ℚ) ≤
        (A : ℚ) * GeneralPaperNativeWorkingSpaceHeadline.spaceScale p *
          (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ e := by
  obtain ⟨A, e, hA⟩ := GeneralPaperMeasuredUnequalStorageRates.profile_headline hg cal K hK hWord
  exact ⟨A, e, fun p hOne phase => (Nat.cast_le.mpr (all_phases hg cal K hWord p phase)).trans (hA p hOne)⟩

end Blotto.GeneralPaperMeasuredUnequalStoragePhases
