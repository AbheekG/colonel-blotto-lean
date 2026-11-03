import Blotto.GeneralPaperOneFieldOriginalResources

/-! One complete bit-preparation headline on original inputs, before any
branch is selected. The common scale is L0+E+nStar^3/epsilon^6. -/
namespace Blotto.GeneralPaperOriginalPreparationTime
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters GeneralPaperOriginalHeadlineTransfers
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem equal_bound (model : RationalCostModel) (p : Input) (cost A e : ℕ)
    (h : cost ≤ A * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
      GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ e) :
    (cost : ℚ) ≤ (A : ℚ) * timeScale p * (logarithm p : ℚ) ^ e := by
  have hQ : (cost : ℚ) ≤ (A : ℚ) * (inputSize p : ℚ) *
      (GeneralPaperEqualInputHeadline.paperLog (equalInput model p) : ℚ) ^ e := by exact_mod_cast h
  have hp : (GeneralPaperEqualInputHeadline.paperLog (equalInput model p) : ℚ) ^ e ≤
      (logarithm p : ℚ) ^ e := by exact_mod_cast Nat.pow_le_pow_left (equal_log model p) e
  have ht : 0 ≤ timeScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (time_positive p)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left (time_ge_input p) (Nat.cast_nonneg A)) hp (by positivity) (by positivity)
  exact hQ.trans hm

theorem from_branches (model : RationalCostModel) (K Ct dt At et : ℕ)
    (hEqual : ∀ p : Input, p.n ≠ 1 → p.budget = 1 → epsilon p < 1 →
      (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤
        Ct * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ dt)
    (hNative : ∀ p : GeneralPaperNativeResourceDomain.Problem, p.n ≠ 1 →
      GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1 →
      ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
        (At : ℚ) * GeneralPaperNativeSourceTimeHeadline.timeScale p *
          (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ et) :
    ∃ C e : ℕ, ∀ p : Input, epsilon p < 1 →
      ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
        (C : ℚ) * timeScale p * (logarithm p : ℚ) ^ e := by
  refine ⟨Ct + At * 4 * 2 ^ et + 2048, dt + et, fun p hOne => ?_⟩
  have ht : 0 ≤ timeScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (time_positive p)
  by_cases hN : p.n = 1
  · exact raise p (timeScale p) ht _ 2048 _ 0 _ (by omega) (by omega)
      (GeneralPaperOneFieldOriginalResources.time model K p hN)
  · by_cases hB : p.budget = 1
    · exact raise p (timeScale p) ht _ Ct _ dt _ (by omega) (by omega)
        (equal_bound model p _ Ct dt (hEqual p hN hB hOne))
    · let strict := strict_of_ne p hB
      have hn := hNative (unequalInput p strict) hN hOne
      have he := congrArg (fun q : Input => (GeneralPaperMeasuredBitDispatch.run model K q).2)
        (original_roundtrip p strict)
      rw [he] at hn
      exact raise p (timeScale p) ht _ (At * 4 * 2 ^ et) _ et _ (by omega) (by omega)
        (native_time_bound p strict _ At et hn)

theorem calibrated_same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ A e : ℕ, ∀ p : Input, epsilon p < 1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
          ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
            (A : ℚ) * timeScale p * (logarithm p : ℚ) ^ e := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, Ct, dt, _Cs, _ds, _Cd, _dd, hEqual⟩ :=
    GeneralPaperMeasuredEqualFullContract.same_return hg
  obtain ⟨At, et, hNative⟩ := GeneralPaperMeasuredUnequalDispatchHeadlines.time_headline hg cal K hK hWord
  have hEqualTime : ∀ p : Input, p.n ≠ 1 → p.budget = 1 → epsilon p < 1 →
      (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤
        Ct * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ dt := by
    intro p hN hB hOne
    obtain ⟨output, hResources⟩ := hEqual p hN hB hOne
    exact hResources.time
  obtain ⟨A, e, hTime⟩ := from_branches model K Ct dt At et hEqualTime hNative
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, A, e, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hGame, hPointwise⟩ := GeneralPaperMeasuredBitDispatch.original_game_contract model K p hOne
  exact ⟨output, hReturn, hGame, hPointwise, hTime p hOne⟩

end Blotto.GeneralPaperOriginalPreparationTime
