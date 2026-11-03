import Blotto.GeneralPaperOriginalStorageTransfers

/-! One calibrated actual original-input return simultaneously satisfies
canonical equilibrium, pointwise budgets, complete bit preparation time,
preparation space and full description size, for all three branches. -/
namespace Blotto.GeneralPaperOriginalPreparationResources
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters GeneralPaperOriginalHeadlineTransfers
open GeneralPaperOriginalStorageContract GeneralPaperOriginalStorageTransfers
set_option autoImplicit false
set_option maxHeartbeats 8500000
set_option maxRecDepth 16384

theorem calibrated_same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ T t S s D e : ℕ, ∀ p : Input, epsilon p < 1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
          ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
            (T : ℚ) * timeScale p * (logarithm p : ℚ) ^ t ∧
          Contract model K S s D e p output := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, Ct, dt, Cs, ds, Cd, dd, hEqual⟩ :=
    GeneralPaperMeasuredEqualFullContract.same_return hg
  obtain ⟨At, et, Ad, hNative⟩ := GeneralPaperMeasuredUnequalDispatchHeadlines.same_return_headlines hg cal K hK hWord
  obtain ⟨As, es, hSpace⟩ := GeneralPaperMeasuredUnequalStoragePhases.headline hg cal K hK hWord
  have hEqTime : ∀ p : Input, p.n ≠ 1 → p.budget = 1 → epsilon p < 1 →
      (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤
        Ct * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ dt := by
    intro p hN hB hOne
    obtain ⟨output, h⟩ := hEqual p hN hB hOne
    exact h.time
  have hNativeTime : ∀ p : GeneralPaperNativeResourceDomain.Problem, p.n ≠ 1 →
      GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1 →
      ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
        (At : ℚ) * GeneralPaperNativeSourceTimeHeadline.timeScale p *
          (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ et := by
    intro p hN hOne
    obtain ⟨output, _, h, _, _⟩ := hNative p hN hOne
    exact h
  obtain ⟨T, t, hTime⟩ := GeneralPaperOriginalPreparationTime.from_branches model K Ct dt At et hEqTime hNativeTime
  let S := Cs + As * 4 * 2 ^ es + 32768
  let s := ds + es
  let D := Cd + Ad * 16 + 1024
  let e := dd + 2
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, fun p hOne => ?_⟩
  suffices h : ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
      (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧ Contract model K S s D e p output by
    obtain ⟨output, hReturn, hResources⟩ := h
    have hGame := GeneralPaperMeasuredBitDispatch.every_returned model K p hOne output hReturn
    exact ⟨output, hReturn, hGame.1, hGame.2, hTime p hOne, hResources⟩
  by_cases hN : p.n = 1
  · exact ⟨(GeneralPaperAllBranchBitDispatch.one p hN).1,
      by rw [GeneralPaperMeasuredBitDispatch.on_one model K p hN],
      one_resources model K S s D e p hN (by dsimp [S]; omega) (by dsimp [D]; omega)⟩
  · by_cases hB : p.budget = 1
    · obtain ⟨output, h⟩ := hEqual p hN hB hOne
      exact ⟨.equal _ output, h.dispatch_returned,
        equal_resources model K Ct dt Cs ds Cd dd S s D e p hN hB output h
          (by dsimp [S]; omega) (by dsimp [s]; omega) (by dsimp [D]; omega) (by dsimp [e]; omega)⟩
    · let strict := strict_of_ne p hB
      let q := unequalInput p strict
      obtain ⟨output, hReturn, _, _, hDescription⟩ := hNative q hN hOne
      have hr : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.unequal output) := hReturn
      rw [hWord] at hDescription
      refine ⟨.unequal output, hr, .unequal hN strict output ?_ ?_⟩
      · exact native_description model K Ad D e p strict output hDescription
          (by dsimp [D]; omega) (by dsimp [e]; omega)
      · intro phase
        have h := native_space_bound p strict _ As es (hSpace q hOne phase)
        have hs := raise p (spaceScale p) ((Nat.cast_nonneg (inputSize p)).trans (space_ge_input p))
          _ (As * 4 * 2 ^ es) S es s (by dsimp [S]; omega) (by dsimp [s]; omega) h
        have hc := GeneralPaperMeasuredUnequalFullContract.phase_capacity hg cal K hWord hNativeSafe q phase
        rw [hWord] at hc
        exact ⟨hs, hc⟩

end Blotto.GeneralPaperOriginalPreparationResources
