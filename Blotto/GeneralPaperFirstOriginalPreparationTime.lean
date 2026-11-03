import Blotto.GeneralPaperFirstEqualDispatchTime

/-! The actual corrected computable all-branch bit entry has the paper
original-input preparation-time headline and canonical continuous laws. -/
namespace Blotto.GeneralPaperFirstOriginalPreparationTime
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters GeneralPaperOriginalHeadlineTransfers
open GeneralPaperOriginalPreparationTime (equal_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem from_branches (model : RationalCostModel) (K Ct dt At et : ℕ)
    (hEqual : ∀ p : Input, p.n ≠ 1 → p.budget = 1 → epsilon p < 1 →
      (GeneralPaperFirstAllBitDispatch.run model K p).2 ≤
        Ct * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ dt)
    (hNative : ∀ p : GeneralPaperNativeResourceDomain.Problem, p.n ≠ 1 →
      GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1 →
      ((GeneralPaperFirstAllBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
        (At : ℚ) * GeneralPaperNativeSourceTimeHeadline.timeScale p *
          (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ et) :
    ∃ C e : ℕ, ∀ p : Input, epsilon p < 1 →
      ((GeneralPaperFirstAllBitDispatch.run model K p).2 : ℚ) ≤
        (C : ℚ) * timeScale p * (logarithm p : ℚ) ^ e := by
  refine ⟨Ct + At * 4 * 2 ^ et + 2048, dt + et, fun p hOne => ?_⟩
  have ht : 0 ≤ timeScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (time_positive p)
  by_cases hN : p.n = 1
  · have hOneTime := GeneralPaperOneFieldOriginalResources.time model K p hN
    rw [← GeneralPaperFirstAllBitDispatch.one_eq_preserved model K p hN] at hOneTime
    exact raise p (timeScale p) ht _ 2048 _ 0 _ (by omega) (by omega) hOneTime
  · by_cases hB : p.budget = 1
    · exact raise p (timeScale p) ht _ Ct _ dt _ (by omega) (by omega)
        (equal_bound model p _ Ct dt (hEqual p hN hB hOne))
    · let strict := strict_of_ne p hB
      have hn := hNative (unequalInput p strict) hN hOne
      have he := congrArg (fun q : Input => (GeneralPaperFirstAllBitDispatch.run model K q).2)
        (original_roundtrip p strict)
      rw [he] at hn
      exact raise p (timeScale p) ht _ (At * 4 * 2 ^ et) _ et _ (by omega) (by omega)
        (native_time_bound p strict _ At et hn)

theorem calibrated_same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ,1≤K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word=GeneralPaperMeasuredReferenceGrowth.word model K ∧ GeneralPaperFirstSharedBitCalibration.EqualSafe model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧ GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ A e : ℕ,∀ p : Input,epsilon p<1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperFirstAllBitDispatch.run model K p).1=some output ∧
          GeneralPaperFirstAllBitLaw.Guarantee model K p output ∧ GeneralPaperFirstAllBitLaw.Pointwise model K p output ∧
          ((GeneralPaperFirstAllBitDispatch.run model K p).2 : ℚ) ≤ (A : ℚ)*timeScale p*(logarithm p : ℚ)^e := by
  obtain ⟨K,hK,cal,hWord,hEqualSafe,hSafe,hNativeSafe⟩ := GeneralPaperFirstSharedBitCalibration.calibrated_reference hg
  obtain ⟨Ct,dt,hEqual⟩ := GeneralPaperFirstEqualDispatchTime.paper_time model ⟨C,d,hg⟩ K hK
  obtain ⟨At,et,hOldNative⟩ := GeneralPaperMeasuredUnequalDispatchHeadlines.time_headline hg cal K hK hWord
  have hNative : ∀ p : GeneralPaperNativeResourceDomain.Problem,p.n≠1 →
      GeneralPaperNativeWorkingSpaceHeadline.epsilon p<1 →
      ((GeneralPaperFirstAllBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
        (At : ℚ)*GeneralPaperNativeSourceTimeHeadline.timeScale p*(GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ)^et := by
    intro p hN hOne
    rw [GeneralPaperFirstAllBitDispatch.unequal_eq_preserved model K (GeneralPaperMeasuredReferenceGrowth.original p)
      hN (ne_of_lt p.budget_valid.2)]
    exact hOldNative p hN hOne
  obtain ⟨A,e,hTime⟩ := from_branches model K Ct dt At et (fun p hN hB _ => hEqual p hN hB) hNative
  refine ⟨K,hK,cal,hWord,hEqualSafe,hSafe,hNativeSafe,A,e,fun p hOne => ?_⟩
  obtain ⟨output,hReturn,hGame,hPointwise⟩ := GeneralPaperFirstAllBitDispatch.original_game_contract model K p hOne
  exact ⟨output,hReturn,hGame,hPointwise,hTime p hOne⟩

end Blotto.GeneralPaperFirstOriginalPreparationTime
