import Blotto.GeneralPaperEpochPhaseCursorCoverage

/-! Every reached native round/epoch frontier is included in the complete
source lifetime observer. Recursive bounds use strict reached indices, and
initialization/returned owners cover zero and terminal prefixes separately.
Append embeds the actual native old/chunk values with its count unchanged.
These statements do not assume a space or reference-width oracle. -/
namespace Blotto.GeneralPaperSourceScopeCoverage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows GeneralPaperStorageCursorPacking
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

theorem local_phase_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch count time : ℕ) (ht : time<count) :
    GeneralPaperLocalSourceLifetimeStorage.phase model W k Qv a c weights Bc Br epoch time≤
      GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch count := by
  have h := scope_phase (GeneralPaperLocalSourceLifetimeStorage.base model W k Qv a weights Bc Br epoch)
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (GeneralPaperLocalSourceLifetimeStorage.phase model W k Qv a c weights Bc Br epoch) count time ht
  rw [←GeneralPaperLocalSourceLifetimeStorage.peak_identity model W k Qv a c weights Bc Br epoch count] at h
  dsimp only [GeneralPaperLocalSourceLifetimeStorage.window]
  omega

theorem source_phase_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch : ℕ) (he : epoch<count) :
    GeneralPaperSourceLifetimeStorage.phase model W k Qv a c hc weights Bc Br epoch≤
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  have h := scope_phase (GeneralPaperSourceLifetimeStorage.base W m a.lambda k)
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (GeneralPaperSourceLifetimeStorage.phase model W k Qv a c hc weights Bc Br) count epoch he
  rw [←GeneralPaperSourceLifetimeStorage.peak_identity model W k Qv a c hc weights Bc Br count] at h
  dsimp only [GeneralPaperSourceLifetimeStorage.window]
  omega

theorem epoch_in_source {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch : ℕ) (he : epoch<count) :
    GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch≤
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  have h := source_phase_covered model W k Qv a c hc weights Bc Br count epoch he
  have hm := Nat.le_max_left (GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch)
    (GeneralPaperSourceLifetimeStorage.appendPeak model W k Qv a c hc weights Bc Br epoch+
      GeneralPaperSourceLifetimeStorage.returnedWindow model W k Qv a c hc weights Bc Br (epoch+1))
  dsimp only [GeneralPaperSourceLifetimeStorage.phase] at h
  omega

theorem round_in_source {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch time : ℕ) (he : epoch<count)
    (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time≤
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  have hl := local_phase_covered model W k Qv a c weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period time ht
  have hround : GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time≤
      GeneralPaperLocalSourceLifetimeStorage.phase model W k Qv a c weights Bc Br epoch time := by
    dsimp only [GeneralPaperLocalSourceLifetimeStorage.phase]
    omega
  exact hround.trans (hl.trans ((GeneralPaperEpochPhaseCursorCoverage.local_loop_covered model W k Qv a c hc weights Bc Br epoch).trans
    (epoch_in_source model W k Qv a c hc weights Bc Br count epoch he)))

theorem field_in_source {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch : ℕ) (he : epoch<count) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    GeneralPaperFieldPreparationPhaseStorage.peak model W a x
      (GeneralPaperEpochCacheConstructionStorage.candidate model W c.controls.source.meshDenominator a x hm).data.codes
      (GeneralPaperEpochCacheConstructionStorage.response model W c.controls.source.meshDenominator a x hm).data.codes≤
        GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count :=
  (GeneralPaperEpochPhaseCursorCoverage.field_covered model W k Qv a c hc weights Bc Br epoch).trans
    (epoch_in_source model W k Qv a c hc weights Bc Br count epoch he)

theorem ready_in_source {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch : ℕ) (he : epoch<count) (response : Bool) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    GeneralPaperReadyPreparationPhaseStorage.peak model W c.controls.source.meshDenominator a response
      (if response then x.mu else x.lambda) hm≤GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count :=
  (GeneralPaperEpochPhaseCursorCoverage.ready_covered model W k Qv a c hc weights Bc Br epoch response).trans
    (epoch_in_source model W k Qv a c hc weights Bc Br count epoch he)

theorem append_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    let first := (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc shared epoch).1.2
    let chunk := (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc shared (treesAt shared a k epoch)).1.2
    ∀ (count : ℕ) (hcount : count≤chunk.size) (_hp : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period),
    GeneralPaperTrajectoryAppendStorage.window W shared.trajectory.rows first chunk count hcount≤
      GeneralPaperSourceLifetimeStorage.appendPeak model W k Qv a c hc weights Bc Br epoch := by
  dsimp only
  intro count hcount hp
  let cursor := counter (GeneralPaperTrajectoryParameters.prepare a.lambda k).period count hp
  have h := observed_le_maximum (GeneralPaperSourceLifetimeStorage.appendWindow model W k Qv a c hc weights Bc Br epoch) cursor
  have heq : GeneralPaperSourceLifetimeStorage.appendWindow model W k Qv a c hc weights Bc Br epoch cursor=
      GeneralPaperTrajectoryAppendStorage.window W (prepare a k Qv weights Bc Br).trajectory.rows
        (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc (prepare a k Qv weights Bc Br) epoch).1.2
        (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc (prepare a k Qv weights Bc Br)
          (treesAt (prepare a k Qv weights Bc Br) a k epoch)).1.2 count hcount := by
    dsimp only [GeneralPaperSourceLifetimeStorage.appendWindow,cursor,counter]
    congr 1
    exact Nat.min_eq_left hcount
  exact heq ▸ h

theorem append_in_source {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count epoch : ℕ) (he : epoch<count) :
    GeneralPaperSourceLifetimeStorage.appendPeak model W k Qv a c hc weights Bc Br epoch≤
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  have h := source_phase_covered model W k Qv a c hc weights Bc Br count epoch he
  have hm := Nat.le_max_right (GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch)
    (GeneralPaperSourceLifetimeStorage.appendPeak model W k Qv a c hc weights Bc Br epoch+
      GeneralPaperSourceLifetimeStorage.returnedWindow model W k Qv a c hc weights Bc Br (epoch+1))
  dsimp only [GeneralPaperSourceLifetimeStorage.phase] at h
  omega

theorem local_initial_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) :
    GeneralPaperLocalSourceLifetimeStorage.initialPeak model W k Qv a weights Bc Br epoch≤
      GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch count := by
  have h := scope_base (GeneralPaperLocalSourceLifetimeStorage.base model W k Qv a weights Bc Br epoch)
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (GeneralPaperLocalSourceLifetimeStorage.phase model W k Qv a c weights Bc Br epoch) count
  rw [←GeneralPaperLocalSourceLifetimeStorage.peak_identity model W k Qv a c weights Bc Br epoch count] at h
  dsimp only [GeneralPaperLocalSourceLifetimeStorage.window,GeneralPaperLocalSourceLifetimeStorage.base] at h ⊢
  omega

theorem source_initial_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    GeneralPaperSourceLifetimeStorage.initialPeak W m a.lambda≤GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  have h := scope_base (GeneralPaperSourceLifetimeStorage.base W m a.lambda k)
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (GeneralPaperSourceLifetimeStorage.phase model W k Qv a c hc weights Bc Br) count
  rw [←GeneralPaperSourceLifetimeStorage.peak_identity model W k Qv a c hc weights Bc Br count] at h
  dsimp only [GeneralPaperSourceLifetimeStorage.window,GeneralPaperSourceLifetimeStorage.base] at h ⊢
  omega

theorem local_terminal_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) :
    GeneralPaperLocalSourceLifetimeStorage.returnedWindow model W k Qv a c weights Bc Br epoch count≤
      GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch count := by
  dsimp only [GeneralPaperLocalSourceLifetimeStorage.window]
  omega

theorem source_terminal_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    GeneralPaperSourceLifetimeStorage.returnedWindow model W k Qv a c hc weights Bc Br count≤
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count := by
  dsimp only [GeneralPaperSourceLifetimeStorage.window]
  omega

theorem reached_round_profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count epoch time : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (hi : epoch<count)
    (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time≤
      GeneralPaperSourceLifetimeStorage.profile model W k Qv a weights Bc Br :=
  (round_in_source model W k Qv a c hc weights Bc Br count epoch time hi ht).trans
    (GeneralPaperSourceLifetimeStorage.bounded model W k Qv a c hc weights Bc Br hw count he)

end Blotto.GeneralPaperSourceScopeCoverage
