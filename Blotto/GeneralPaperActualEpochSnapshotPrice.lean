import Blotto.GeneralPaperEpochSnapshotFamilyPrice
import Blotto.GeneralPaperActualForestUpdate

/-! Actual retained local states supply every snapshot premise. Time-indexed
state expressions identify source returns; no local execution is replayed.
-/
namespace Blotto.GeneralPaperActualEpochSnapshotPrice
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem selected_fields {m k : ℕ} (cache : Cache m k) (Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    ∀ j,GeneralPaperEpochFieldState.Bounded ((stateAt (selected cache Qv weights Bc Br) time).fields.read j)
      c.controls.precision.levelBound := by
  intro j
  have h := selected_cap cache Qv weights Bc Br time ht j
  rw [hc]
  exact h

theorem selected_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) :
    (GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c (stateAt (selected cache Qv weights Bc Br) time).fields).1=
      beforeAt (selected cache Qv weights Bc Br) time := by
  rw [GeneralPaperEpochSnapshotFamilyPrice.data bits index price W cache.alphabet.lambda Qv c hc,hc]
  rfl

theorem selected_work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let fields := (stateAt (selected cache Qv weights Bc Br) time).fields
    (GeneralPaperEpochSnapshotFamilyPrice.run true (fun w => w) model.rat W c fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.profile model.rat W m cache.alphabet.lambda k Qv ∧
    (GeneralPaperEpochSnapshotFamilyPrice.run false (fun _ => 1) model.rat 1 c fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.arithmeticProfile m cache.alphabet.lambda k Qv := by
  have hf := selected_fields cache Qv c hc weights Bc Br time ht
  exact ⟨GeneralPaperEpochSnapshotFamilyPrice.bit_work model.rat model.monotone W cache.alphabet.lambda Qv c hc _ hf,
    GeneralPaperEpochSnapshotFamilyPrice.arithmetic_work model.rat cache.alphabet.lambda Qv c hc _ hf⟩

theorem selected_positive {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    GeneralPaperEpochSnapshot.Positive ((GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c
      (stateAt (selected cache Qv weights Bc Br) time).fields).1.read j) := by
  rw [selected_data bits index price W Qv cache c hc]
  exact GeneralPaperCatalogueEpochRun.selected_positive cache Qv weights Bc Br time ht j

theorem selected_coherent {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    GeneralPaperEpochSnapshot.Coherent ((GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c
      (stateAt (selected cache Qv weights Bc Br) time).fields).1.read j) := by
  rw [selected_data bits index price W Qv cache c hc]
  exact snapshot_coherent (selected cache Qv weights Bc Br) time j

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let fields := (stateAt (epochRun shared a k trees) time).fields
    (GeneralPaperEpochSnapshotFamilyPrice.run true (fun w => w) model.rat W c fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.profile model.rat W m a.lambda k Qv ∧
    (GeneralPaperEpochSnapshotFamilyPrice.run false (fun _ => 1) model.rat 1 c fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.arithmeticProfile m a.lambda k Qv := by
  dsimp only
  rw [epochRun_selected]
  exact selected_work model W Qv _ c hc weights Bc Br time ht

theorem epoch_data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let current := epochRun shared a k trees
    (GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c (stateAt current time).fields).1=beforeAt current time := by
  dsimp only
  rw [epochRun_selected]
  exact selected_data bits index price W Qv _ c hc weights Bc Br time

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let fields := (stateAt (epochRun shared a k trees) time).fields
    (GeneralPaperEpochSnapshotFamilyPrice.run true (fun w => w) model.rat W ready.2.source fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.profile model.rat W m a.lambda k Qv ∧
    (GeneralPaperEpochSnapshotFamilyPrice.run false (fun _ => 1) model.rat 1 ready.2.source fields).2≤
      GeneralPaperEpochSnapshotFamilyPrice.arithmeticProfile m a.lambda k Qv := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br epoch time ht

end Blotto.GeneralPaperActualEpochSnapshotPrice
