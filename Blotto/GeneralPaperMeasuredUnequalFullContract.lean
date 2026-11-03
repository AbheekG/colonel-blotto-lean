import Blotto.GeneralPaperMeasuredUnequalStorageCalibration

/-! Same-return unequal paper contracts, now including complete preparation
phase space and one uniform capacity calibration for all retained frames. -/
namespace Blotto.GeneralPaperMeasuredUnequalFullContract
open GeneralPaperNativeResourceDomain
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon paperLog spaceScale)
open GeneralPaperNativeSourceTimeHeadline (timeScale)
open GeneralPaperMeasuredUnequalStorageCalibration (nativeEnvelope)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def Safe (model : RationalCostModel) (C d K : ℕ) : Prop :=
  ∀ p : GeneralPaperOriginalGameInput.Input,
    let ep := GeneralPaperOriginalGameInput.equalInput model p
    let W := GeneralPaperEqualInputDomain.word K ep
    GeneralPaperStoredPreparationUniformCapacity.envelope model K ep +
      GeneralPaperMixedInitializerPhases.profile model W K ep + nativeEnvelope model C d W K p < 2 ^ W

theorem calibrated_reference {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧ Safe model C d K := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperMeasuredUnequalStorageCalibration.joint_capacity hg
  let cal : Reference model C d :=
    ⟨GeneralPaperMeasuredReferenceGrowth.word model K, GeneralPaperMeasuredReferenceGrowth.positive model K hK,
      GeneralPaperMeasuredReferenceGrowth.word_tight model K,
      fun p => (hSafe (GeneralPaperMeasuredReferenceGrowth.original p)).2 p.budget_valid.2⟩
  exact ⟨K, hK, cal, rfl, fun p => (hSafe p).1⟩

theorem phase_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (hSafe : Safe model C d K)
    (p : Problem) (phase : GeneralPaperMeasuredUnequalStoragePhases.Phase model K p) :
    GeneralPaperMeasuredUnequalStoragePhases.window model K p phase < 2 ^ cal.word p := by
  have hs := hSafe (GeneralPaperMeasuredReferenceGrowth.original p)
  dsimp only at hs
  have hw : GeneralPaperEqualInputDomain.word K
      (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) = cal.word p :=
    (congrFun hWord p).symm
  rw [hw] at hs
  have he : GeneralPaperMeasuredUnequalCapacityEnvelope.envelope model C d (cal.word p) K p ≤
      nativeEnvelope model C d (cal.word p) K (GeneralPaperMeasuredReferenceGrowth.original p) := by
    dsimp only [nativeEnvelope]
    split_ifs with h
    · exact le_rfl
    · exact (h p.budget_valid.2).elim
  have hCapacity : GeneralPaperMeasuredUnequalCapacityEnvelope.envelope model C d (cal.word p) K p <
      2 ^ cal.word p := by omega
  exact (GeneralPaperMeasuredUnequalCapacityEnvelope.all_phases hg cal K hWord p phase).trans_lt hCapacity

theorem same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧ Safe model C d K ∧
      ∃ At et Ad As es : ℕ, ∀ p : Problem, p.n ≠ 1 → epsilon p < 1 →
        ∃ output : GeneralPaperClosedStrategyDriver.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).1 =
            some (.unequal output) ∧
          output = GeneralPaperMeasuredUnequalSampling.actual model K p ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K (GeneralPaperMeasuredReferenceGrowth.original p) (.unequal output) ∧
          GeneralPaperAllBranchBitOutput.Pointwise model K (GeneralPaperMeasuredReferenceGrowth.original p) (.unequal output) ∧
          ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
            (At : ℚ) * timeScale p * (paperLog p : ℚ) ^ et ∧
          GeneralPaperArbitraryPreparationDraw.Contract model C d p output ∧
          GeneralPaperArbitraryPreparationDraw.Independent model p output ∧
          GeneralPaperMeasuredUnequalDispatchHeadlines.DescriptionBound model (cal.word p) Ad p output ∧
          ∀ phase : GeneralPaperMeasuredUnequalStoragePhases.Phase model K p,
            (GeneralPaperMeasuredUnequalStoragePhases.window model K p phase : ℚ) ≤
              (As : ℚ) * spaceScale p * (paperLog p : ℚ) ^ es ∧
            GeneralPaperMeasuredUnequalStoragePhases.window model K p phase < 2 ^ cal.word p := by
  obtain ⟨K, hK, cal, hWord, hSafe⟩ := calibrated_reference hg
  obtain ⟨At, et, Ad, hAll⟩ := GeneralPaperMeasuredUnequalDispatchHeadlines.same_return_headlines hg cal K hK hWord
  obtain ⟨As, es, hSpace⟩ := GeneralPaperMeasuredUnequalStoragePhases.headline hg cal K hK hWord
  refine ⟨K, hK, cal, hWord, hSafe, At, et, Ad, As, es, fun p hN hOne => ?_⟩
  obtain ⟨output, hReturn, hTime, hDraw, hDescription⟩ := hAll p hN hOne
  have hGame := GeneralPaperMeasuredBitDispatch.every_returned model K (GeneralPaperMeasuredReferenceGrowth.original p)
    hOne (.unequal output) hReturn
  have hActual : (GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).1 =
      some (.unequal (GeneralPaperMeasuredUnequalSampling.actual model K p)) := by
    rw [GeneralPaperMeasuredBitDispatch.on_unequal model K (GeneralPaperMeasuredReferenceGrowth.original p)
      hN (ne_of_lt p.budget_valid.2)]
    rfl
  have hEq : output = GeneralPaperMeasuredUnequalSampling.actual model K p :=
    GeneralPaperAllBranchBitDispatch.Prepared.unequal.inj (Option.some.inj (hReturn.symm.trans hActual))
  exact ⟨output, hReturn, hEq, hGame.1, hGame.2, hTime, hDraw,
    GeneralPaperArbitraryPreparationDraw.independent_of_draw p output hDraw, hDescription,
    fun phase => ⟨hSpace p hOne phase, phase_capacity hg cal K hWord hSafe p phase⟩⟩

end Blotto.GeneralPaperMeasuredUnequalFullContract
