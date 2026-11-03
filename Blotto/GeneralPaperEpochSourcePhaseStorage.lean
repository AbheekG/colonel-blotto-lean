import Blotto.GeneralPaperReadyPreparationPhaseStorage

/-! Native epoch frontier: summary/cache and forest-update parents retain
their full context while one Ready/field child or local loop is active.
All phase maxima have finite native cursors. The full native epoch return
retains only the updated forest and row chunk; no cache history is charged.
The outer source recursion/global reference calibration remains separate. -/
namespace Blotto.GeneralPaperEpochSourcePhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun GeneralPaperFiniteStorageWindows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def learner (i : Fin 4) : GeneralPaperCatalogueOccurrenceHistory.Learner :=
  if i.val=0 then .p else if i.val=1 then .q else if i.val=2 then .lambda else .mu

abbrev ParentCursor (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) :=
  Fin (m+1) × Fin (c.controls.source.summarySize+1) ×
    Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) ×
    Fin ((((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)+1) ×
    Fin (GeneralPaperRoundPhaseStorage.progressCap m lambda k Qv+1) × Fin m ×
    Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2) ×
    Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) × Fin c.controls.source.summarySize × Fin 4

def parentWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (cursor : ParentCursor m a.lambda k Qv c) : ℕ :=
  let ⟨count,inner,row,tailCount,remaining,j,i,q,r,which⟩ := cursor
  GeneralPaperActualEpochParentStorage.window model W k Qv a c hc weights Bc Br epoch
    count.val inner.val row.val tailCount.val remaining.val (Nat.le_of_lt_succ count.isLt)
    (Nat.le_of_lt_succ inner.isLt) (Nat.le_of_lt_succ row.isLt) (Nat.le_of_lt_succ tailCount.isLt) j i q r (learner which)

def parents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  maximum (parentWindow model W k Qv a c hc weights Bc Br epoch)

theorem parents_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    parents model W k Qv a c hc weights Bc Br epoch≤GeneralPaperActualEpochParentStorage.profile model W m k Qv a := by
  apply maximum_bound
  intro cursor
  rcases cursor with ⟨count,inner,row,tailCount,remaining,j,i,q,r,which⟩
  exact GeneralPaperActualEpochParentStorage.actual model W k Qv a c hc weights Bc Br epoch
    count.val inner.val row.val tailCount.val remaining.val he (Nat.le_of_lt_succ count.isLt)
    (Nat.le_of_lt_succ inner.isLt) (Nat.le_of_lt_succ row.isLt) (Nat.le_of_lt_succ tailCount.isLt) j i q r (learner which)

def cacheChildren {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
  let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
  let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
  max (max (GeneralPaperReadyPreparationPhaseStorage.peak model W c.controls.source.meshDenominator a false x.lambda hm)
      (GeneralPaperReadyPreparationPhaseStorage.peak model W c.controls.source.meshDenominator a true x.mu hm))
    (GeneralPaperFieldPreparationPhaseStorage.peak model W a x
      (GeneralPaperEpochCacheConstructionStorage.candidate model W c.controls.source.meshDenominator a x hm).data.codes
      (GeneralPaperEpochCacheConstructionStorage.response model W c.controls.source.meshDenominator a x hm).data.codes)

def childrenProfile (model : RationalCostModel) (W m k : ℕ) (a : Alphabet) : ℕ :=
  max (GeneralPaperReadyPreparationPhaseStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a)
    (GeneralPaperFieldPreparationPhaseStorage.profile model W m k a)

theorem children_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    cacheChildren model W k Qv a c hc weights Bc Br epoch≤childrenProfile model W m k a :=
  max_le_max (GeneralPaperReadyPreparationPhaseStorage.native_tree_arrays model W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he))
    (GeneralPaperFieldPreparationPhaseStorage.native_tree_arrays model W m k Qv a c hc _ _
      (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
      (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he))

def returnedWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let value := (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc shared (treesAt shared a k epoch)).1
  GeneralPaperEncodedForestStorage.footprint W value.1+
    GeneralPaperEncodedTrajectoryStorage.footprint W shared.trajectory.period value.2+64*W

def returnedProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedForestStorage.profile W m lambda k Qv+GeneralPaperLocalTrajectoryStorage.profile W m lambda k+64*W

theorem returned_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    returnedWindow model W k Qv a c hc weights Bc Br epoch≤returnedProfile W m a.lambda k Qv := by
  let shared := prepare a k Qv weights Bc Br
  have hf := GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br (epoch+1) he
  have hr := GeneralPaperLocalTrajectoryStorage.selected W Qv
    (GeneralPaperCatalogueShared.cache shared a k (treesAt shared a k epoch)) weights Bc Br
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period (Nat.le_refl _)
  unfold returnedWindow
  dsimp only
  rw [GeneralPaperOuterEpochExecution.data true (fun w => w) model W k Qv a c hc weights Bc Br epoch he]
  exact Nat.add_le_add_right (Nat.add_le_add hf hr) _

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  GeneralPaperEncodedSharedSource.footprint W (prepare a k Qv weights Bc Br)+
    GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period+
    parents model W k Qv a c hc weights Bc Br epoch+
    max (cacheChildren model W k Qv a c hc weights Bc Br epoch)
      (GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)+
    returnedWindow model W k Qv a c hc weights Bc Br epoch+256*W

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv+
    GeneralPaperActualEpochParentStorage.profile model W m k Qv a+
    max (childrenProfile model W m k a) (GeneralPaperLocalSourceLifetimeStorage.profile model W k Qv a weights Bc Br)+
    returnedProfile W m a.lambda k Qv+256*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    window model W k Qv a c hc weights Bc Br epoch≤profile model W k Qv a weights Bc Br := by
  have hs := GeneralPaperSharedResidentStorage.actual W k Qv a weights Bc Br epoch
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period (by omega) (Nat.le_refl _)
  have hp := parents_bound model W k Qv a c hc weights Bc Br epoch he
  have hc' := children_bound model W k Qv a c hc weights Bc Br epoch (by omega)
  have hl := GeneralPaperLocalSourceLifetimeStorage.bounded model W k Qv a c hc weights Bc Br hw epoch
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period (by omega) (Nat.le_refl _)
  have hr := returned_bound model W k Qv a c hc weights Bc Br epoch he
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs hp) (max_le_max hc' hl)) hr) _

end Blotto.GeneralPaperEpochSourcePhaseStorage
