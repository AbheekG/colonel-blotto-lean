import Blotto.GeneralPaperOneFieldBitOutput

/-! Sampling contracts carried by the same tagged original-input return.
The equal branch keeps the actual RAM-root law, expected work and random
reads; unequal sampling keeps bounded work and exact fresh-bit counts.
The one-field copy emits its full rational row without randomness. -/
namespace Blotto.GeneralPaperOriginalSamplingContract
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
open GeneralPaperAllBranchBitDispatch (Prepared one)
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def OneField (p : Input) : Prop := ∀ poor : Bool,
  (GeneralPaperOneFieldBitOutput.run p poor).reads = 0 ∧
  (GeneralPaperOneFieldBitOutput.run p poor).work ≤ 512 * GeneralPaperOneFieldBitOutput.originalSize p ∧
  ∃ output : RationalResourceArray 1,
    (GeneralPaperOneFieldBitOutput.run p poor).output = some output ∧
    (∀ j, output.allocation j = GeneralPaperOneFieldBitOutput.budget p poor) ∧
    (∑ j : Fin 1, rationalWordWidth (output.allocation j)) =
      rationalWordWidth (GeneralPaperOneFieldBitOutput.budget p poor) ∧
    FullBudget (GeneralPaperOneFieldBitOutput.budget p poor : ℝ) output.realAllocation

inductive Contract (model : RationalCostModel) (C d K : ℕ) (p : Input) : Prepared p.n → Prop
  | oneField (hN : p.n = 1) (output : OneField p)
      (independent : GeneralPaperOneFieldBitOutput.Independent model K p hN) :
      Contract model C d K p (one p hN).1
  | equal (hN : p.n ≠ 1) (hB : p.budget = 1)
      (output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)))
      (sampling : GeneralPaperStoredPipelineSamplingContract.Contract model 1 K (equalInput model p) output)
      (independent : GeneralPaperMeasuredEqualFullContract.Independent model K (equalInput model p) output) :
      Contract model C d K p (.equal _ output)
  | unequal (hN : p.n ≠ 1) (hStrict : p.budget < 1)
      (output : GeneralPaperClosedStrategyDriver.Prepared p.n)
      (sampling : GeneralPaperArbitraryPreparationDraw.Contract model C d (unequalInput p hStrict) output)
      (independent : GeneralPaperArbitraryPreparationDraw.Independent model (unequalInput p hStrict) output) :
      Contract model C d K p (.unequal output)

theorem one_field (p : Input) : OneField p := by
  intro poor
  exact ⟨GeneralPaperOneFieldBitOutput.reads p poor, GeneralPaperOneFieldBitOutput.input_linear p poor,
    GeneralPaperOneFieldBitOutput.written p poor⟩

theorem every_returned {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (K : ℕ) (p : Input) (hOne : epsilon p < 1)
    (output : Prepared p.n) (hReturn : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output) :
    Contract model C d K p output := by
  by_cases hN : p.n = 1
  · have hr := GeneralPaperMeasuredBitDispatch.on_one model K p hN
    have he : output = (one p hN).1 := by
      rw [hr] at hReturn
      exact (Option.some.inj hReturn).symm
    rw [he]
    exact .oneField hN (one_field p) (GeneralPaperOneFieldBitOutput.independent model K p hN)
  · by_cases hB : p.budget = 1
    · obtain ⟨actual, hMeasured, hPipeline⟩ := GeneralPaperMeasuredEqualPreparation.returns model 1 K p
      have hr : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.equal _ actual) := by
        rw [GeneralPaperMeasuredBitDispatch.on_equal model K p hN hB]
        exact hMeasured
      have he := Option.some.inj (hReturn.symm.trans hr)
      rw [he]
      exact .equal hN hB actual
        (GeneralPaperStoredPipelineSamplingContract.every_returned model 1 K (equalInput model p) actual hPipeline)
        (GeneralPaperStoredPipelineSamplingContract.independent_players model 1 K (equalInput model p) actual)
    · let strict := strict_of_ne p hB
      let q := unequalInput p strict
      let actual := GeneralPaperMeasuredUnequalSampling.actual model K q
      have hr : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.unequal actual) := by
        rw [GeneralPaperMeasuredBitDispatch.on_unequal model K p hN hB]
        rfl
      have he := Option.some.inj (hReturn.symm.trans hr)
      rw [he]
      have hDraw := GeneralPaperMeasuredUnequalSampling.draw_contract hg K q hOne
      exact .unequal hN strict actual hDraw (GeneralPaperArbitraryPreparationDraw.independent_of_draw q actual hDraw)

theorem calibrated_same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ T t S s D e : ℕ, ∀ p : Input, epsilon p < 1 →
        ∃ output : Prepared p.n, (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
          ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
            (T : ℚ) * timeScale p * (logarithm p : ℚ) ^ t ∧
          GeneralPaperOriginalStorageContract.Contract model K S s D e p output ∧
          Contract model C d K p output := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, hAll⟩ :=
    GeneralPaperOriginalPreparationResources.calibrated_same_return hg
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hGame, hPointwise, hTime, hStorage⟩ := hAll p hOne
  exact ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, every_returned hg K p hOne output hReturn⟩

end Blotto.GeneralPaperOriginalSamplingContract
