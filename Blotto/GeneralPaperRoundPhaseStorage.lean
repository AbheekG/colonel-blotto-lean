import Blotto.GeneralPaperFiniteStorageWindows

/-! Closed finite phase windows of one reached native round. Extrema over
constructor prefixes and active callbacks use native source capacities.
Full DP/output phases are present independently of field callbacks, including
empty families. No phase-space value is supplied to the execution. -/
namespace Blotto.GeneralPaperRoundPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def progressCap (m lambda k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m lambda k Qv
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  m+(GeneralPaperSourceParameters.prepare k).summarySize+GeneralPaperBatchCounterPrice.limit k+
    p.grid.size+p.parameters.leafCount+t.period+t.epochs+64

theorem native_caps (m lambda k Qv : ℕ) :
    ∀ x∈[m,(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+2,GeneralPaperBatchCounterPrice.limit k,
      GeneralPaperBatchCounterPrice.limit k+1,(GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size,
      (GeneralPaperProfitParameters.prepare m lambda k Qv).parameters.leafCount,
      (GeneralPaperTrajectoryParameters.prepare lambda k).period,(GeneralPaperTrajectoryParameters.prepare lambda k).epochs,64],
      x≤progressCap m lambda k Qv := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx <;> rw [hx] <;> dsimp only [progressCap] <;> omega

abbrev CallbackCursor (m lambda k Qv : ℕ) :=
  Fin m × Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2) ×
    Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) × Fin (m+1) ×
    Fin (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size ×
    Fin (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size ×
    Fin (progressCap m lambda k Qv+1) × Fin (progressCap m lambda k Qv+1)

def callbackWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) (cursor : CallbackCursor m a.lambda k Qv) : ℕ :=
  let ⟨j,i,count,row,left,right,copied,inner⟩ := cursor
  GeneralPaperSelectedRowConstructionStorage.sourceWindow model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time
    j i count.val copied.val row.val (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ row.isLt) left right inner.val

def callbacks {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  maximum (callbackWindow model W k Qv a weights Bc Br epoch time)

theorem callbacks_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    callbacks model W k Qv a weights Bc Br epoch time≤GeneralPaperSelectedRowConstructionStorage.sourceProfile model W k Qv a weights Bc Br := by
  apply maximum_bound
  intro cursor
  rcases cursor with ⟨j,i,count,row,left,right,copied,inner⟩
  exact GeneralPaperSelectedRowConstructionStorage.actual model W k Qv a weights Bc Br hw epoch time he ht
    j i count.val copied.val row.val (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ row.isLt) left right inner.val

abbrev SnapshotCursor (m lambda k Qv : ℕ) :=
  Fin (m+1) × Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1) ×
    Fin (progressCap m lambda k Qv+1) × Fin (progressCap m lambda k Qv+1)

def snapshotWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch time : ℕ) (cursor : SnapshotCursor m a.lambda k Qv) : ℕ :=
  let ⟨count,inner,used,copied⟩ := cursor
  let shared := prepare a k Qv weights Bc Br
  let current := epochRun shared a k (GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch)
  GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields
    count.val inner.val used.val copied.val (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ inner.isLt)

def snapshots {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  maximum (snapshotWindow model W k Qv a c weights Bc Br epoch time)

theorem snapshots_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    snapshots model W k Qv a c weights Bc Br epoch time≤GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv := by
  apply maximum_bound
  intro cursor
  rcases cursor with ⟨count,inner,used,copied⟩
  exact GeneralPaperActualSnapshotConstructionStorage.actual model W k Qv a c hc weights Bc Br
    epoch time count.val inner.val used.val copied.val ht (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ inner.isLt)

def selectorWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) (count : Fin (m+1)) : ℕ :=
  GeneralPaperActualDPConstructionStorage.window true (fun w => w) model.rat W W k Qv a (prepare a k Qv weights Bc Br)
    weights Bc Br epoch time count.val (Nat.le_of_lt_succ count.isLt)

def selectors {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  maximum (selectorWindow model W k Qv a weights Bc Br epoch time)

theorem selectors_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    selectors model W k Qv a weights Bc Br epoch time≤GeneralPaperActualDPConstructionStorage.profile W k Qv a weights Bc Br := by
  apply maximum_bound
  intro count
  exact GeneralPaperActualDPConstructionStorage.actual true (fun w => w) model.rat W W k Qv a weights Bc Br hw
    epoch time count.val he ht (Nat.le_of_lt_succ count.isLt)

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  max (snapshots model W k Qv a c weights Bc Br epoch time)
    (max (selectors model W k Qv a weights Bc Br epoch time) (callbacks model W k Qv a weights Bc Br epoch time))+256*W

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  max (GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv)
    (max (GeneralPaperActualDPConstructionStorage.profile W k Qv a weights Bc Br)
      (GeneralPaperSelectedRowConstructionStorage.sourceProfile model W k Qv a weights Bc Br))+256*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    window model W k Qv a c weights Bc Br epoch time≤profile model W k Qv a weights Bc Br :=
  Nat.add_le_add_right (max_le_max (snapshots_bound model W k Qv a c hc weights Bc Br epoch time (by omega))
    (max_le_max (selectors_bound model W k Qv a weights Bc Br hw epoch time he (by omega))
      (callbacks_bound model W k Qv a weights Bc Br hw epoch time he ht))) _

end Blotto.GeneralPaperRoundPhaseStorage
