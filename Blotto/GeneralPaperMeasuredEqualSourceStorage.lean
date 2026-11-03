import Blotto.GeneralPaperMeasuredEqualSourceParents

/-! Actual smaller-charge initialization and selected source preparation.
Every native component keeps the same word; only saved initializer fields
are repriced, and the parsed return retains its two word references. -/
namespace Blotto.GeneralPaperMeasuredEqualSourceStorage
open GeneralPaperEqualInputDomain
open GeneralPaperMeasuredEqualSourceParents
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

noncomputable def dispatchWindow (model : RationalCostModel) (S A K : ℕ) (p : Input model) :
    GeneralPaperEqualDispatchLifetime.Phase model S p → ℕ
  | .initialization phase => GeneralPaperMixedInitializerPhases.window model S A K p phase + dispatchParent model S A K p
  | .initialPrefix phase => GeneralPaperMixedInitializerControls.returnedOwner model S A K p +
      GeneralPaperEqualInitialPrefixLifetime.window model S S p.k p.values p.budget phase + dispatchParent model S A K p
  | .scan cursor _ => GeneralPaperMixedInitializerControls.returnedOwner model S A K p +
      GeneralPaperEqualInitialPrefixLifetime.window model S S p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model S (GeneralPaperEqualDispatchLifetime.lengths model S p) cursor + dispatchParent model S A K p
  | .vertex chosen cursor h => GeneralPaperMixedInitializerControls.returnedOwner model S A K p +
      GeneralPaperEqualInitialPrefixLifetime.window model S S p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model S (GeneralPaperEqualDispatchLifetime.lengths model S p) p.n +
      GeneralPaperEqualBitVertexLifetime.window S p.budget chosen cursor h + dispatchParent model S A K p
  | .groupedNative small phase => GeneralPaperMixedInitializerControls.returnedOwner model S A K p +
      GeneralPaperEqualInitialPrefixLifetime.window model S S p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model S (GeneralPaperEqualDispatchLifetime.lengths model S p) p.n +
      GeneralPaperEqualFullInitializationResources.window model S K (grouped p small) (.inr phase) + dispatchParent model S A K p
  | .returned => GeneralPaperMixedInitializerControls.returnedOwner model S A K p +
      GeneralPaperEqualInitialPrefixLifetime.window model S S p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model S (GeneralPaperEqualDispatchLifetime.lengths model S p) p.n +
      GeneralPaperEqualDispatchLocalRates.vertexProfile S p + GeneralPaperEqualDispatchLifetime.groupedProfile model S K p + dispatchParent model S A K p

theorem dispatch_le (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model)
    (phase : GeneralPaperEqualDispatchLifetime.Phase model S p) :
    dispatchWindow model S A K p phase ≤ GeneralPaperEqualDispatchLifetime.window model S K p phase +
      GeneralPaperMixedInitializerPhases.profile model S K p + 2 * S := by
  have hp := dispatch_parent_bound model S A K h p
  have hr := returned_owner model S A K h p
  cases phase with
  | initialization phase =>
    have hi := GeneralPaperMixedInitializerPhases.all_phases model S A K h p phase
    dsimp only [dispatchWindow, GeneralPaperEqualDispatchLifetime.window]
    omega
  | _ =>
    dsimp only [dispatchWindow, GeneralPaperEqualDispatchLifetime.window]
    all_goals omega

noncomputable def window (model : RationalCostModel) (S A K : ℕ) (p : Input model) :
    GeneralPaperEqualSelectedPreparationResources.Phase model S p → ℕ
  | .inl phase => dispatchWindow model S A K p phase + selectedParent model S A K p
  | .inr phase => dispatchWindow model S A K p .returned +
      GeneralPaperEqualSelectedClosureLifetime.window model S p.k p.budget
        (GeneralPaperEqualSelectedPreparationResources.branch model S p) phase + selectedParent model S A K p

theorem window_le (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model)
    (phase : GeneralPaperEqualSelectedPreparationResources.Phase model S p) :
    window model S A K p phase ≤ GeneralPaperEqualSelectedPreparationResources.window model S K p phase +
      GeneralPaperMixedInitializerPhases.profile model S K p + 2 * S := by
  have hp := selected_parent_bound model S A K h p
  cases phase with
  | inl phase =>
    have hd := dispatch_le model S A K h p phase
    dsimp only [window, GeneralPaperEqualSelectedPreparationResources.window]
    omega
  | inr phase =>
    have hd := dispatch_le model S A K h p .returned
    dsimp only [window, GeneralPaperEqualSelectedPreparationResources.window]
    omega

end Blotto.GeneralPaperMeasuredEqualSourceStorage
