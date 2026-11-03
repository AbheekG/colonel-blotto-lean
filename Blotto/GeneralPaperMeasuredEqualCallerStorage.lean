import Blotto.GeneralPaperMeasuredEqualSourceStorage

/-! Actual pre-copy/copied owners, smaller saved prices, final attachment
and selected construction inputs coexist with the retained parsed result. -/
namespace Blotto.GeneralPaperMeasuredEqualCallerStorage
open GeneralPaperEqualInputDomain
open GeneralPaperMeasuredEqualRepricing (selected_data copied_data)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def sourceOwners (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.inputOwner model (word K p) p +
    GeneralPaperPreparationSourceOwners.owner (word K p) (GeneralPaperEqualSelectedPipeline.run model A K p).1 +
    GeneralPaperPreparationSourceOwners.owner (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1

theorem source_owners_eq (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    sourceOwners model A K p = GeneralPaperPreparationSourceOwners.window model K p := by
  dsimp only [sourceOwners, GeneralPaperPreparationSourceOwners.window]
  rw [selected_data model A (word K p) K p, copied_data model A (word K p) K p]

def resultWindow (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  let source := (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1
  let actual := GeneralPaperStoredSelectedConstruction.run model (word K p) source
  actual.1.elim 0 (fun output => GeneralPaperResultAttachmentLifetime.window (word K p) source.address
    (GeneralPaperEqualCopiedPipeline.run model A K p).2 output)

theorem result_window_le (model : RationalCostModel) (A K : ℕ) (p : Input model) (h : A ≤ word K p) :
    resultWindow model A K p ≤ GeneralPaperPreparationCallerLifetime.resultWindow model K p := by
  have hm := GeneralPaperMeasuredEqualWork.copied_mono model A (word K p) K h p
  dsimp only [resultWindow, GeneralPaperPreparationCallerLifetime.resultWindow]
  cases he : (GeneralPaperStoredSelectedConstruction.run model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1).1 with
  | none => simp only [Option.elim_none, le_refl]
  | some output =>
    simp only [Option.elim_some]
    exact GeneralPaperMeasuredEqualRepricing.attachment_mono _ _ _ hm output

def window (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  sourceOwners model A K p + GeneralPaperMeasuredEqualSourceParents.callerWindow model A K p + resultWindow model A K p +
    GeneralPaperSelectedOuterInputLifetime.combinedWindow model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 +
    GeneralPaperMixedInitializerControls.returnedOwner model (word K p) A K p

theorem window_le (model : RationalCostModel) (A K : ℕ) (p : Input model) (h : A ≤ word K p) :
    window model A K p ≤ GeneralPaperStoredPreparationCallerLifetime.window model K p +
      GeneralPaperMixedInitializerPhases.profile model (word K p) K p := by
  have hc := GeneralPaperMeasuredEqualSourceParents.caller_bound model A K p h
  have hr := result_window_le model A K p h
  have hi := GeneralPaperMixedInitializerPhases.all_phases model (word K p) A K h p .returned
  dsimp only [GeneralPaperMixedInitializerPhases.window, GeneralPaperMixedInitializerPhases.component] at hi
  dsimp only [window, GeneralPaperStoredPreparationCallerLifetime.window, GeneralPaperPreparationCallerLifetime.window]
  rw [source_owners_eq, copied_data model A (word K p) K p]
  omega

end Blotto.GeneralPaperMeasuredEqualCallerStorage
