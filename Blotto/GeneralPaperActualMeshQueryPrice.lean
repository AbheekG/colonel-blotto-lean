import Blotto.GeneralPaperActualMeshPrefixInvariant

/-! Complete point/interval query prices at reached local snapshots. Both
models borrow the retained mesh and caches. These observer identities join
existing executions; they do not execute a second epoch or snapshot pass.
-/
namespace Blotto.GeneralPaperActualMeshQueryPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem prefix_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (learner : Learner)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n) :
    let prefixes := (block learner (snapshotAt (selected cache Qv weights Bc Br) time j)).cdf
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes ranks q).2≤
      GeneralPaperCachedMeshPrefixQuery.cachedProfile model.rat W m cache.alphabet.lambda k Qv ∧
    (GeneralPaperCachedMeshPrefixQuery.cached false (fun _ => 1) 1 mesh prefixes ranks q).2≤
      GeneralPaperCachedMeshPrefixQuery.cachedArithmeticProfile k := by
  have hg := GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  exact ⟨GeneralPaperCachedMeshPrefixQuery.cached_bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _ ranks q hm hg,
    GeneralPaperCachedMeshPrefixQuery.cached_arithmetic_work _ _ ranks q⟩

theorem interval_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (learner : Learner)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n) :
    let prefixes := (block learner (snapshotAt (selected cache Qv weights Bc Br) time j)).cdf
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes ranks lo hi).2≤
      GeneralPaperCachedMeshIntervalQuery.cachedProfile model.rat W m cache.alphabet.lambda k Qv ∧
    (GeneralPaperCachedMeshIntervalQuery.cached false (fun _ => 1) 1 mesh prefixes ranks lo hi).2≤
      GeneralPaperCachedMeshIntervalQuery.cachedArithmeticProfile k := by
  have hg := GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  exact ⟨GeneralPaperCachedMeshIntervalQuery.cached_bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _ ranks lo hi hm hg,
    GeneralPaperCachedMeshIntervalQuery.cached_arithmetic_work _ _ ranks lo hi⟩

theorem epoch_good {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m) (learner : Learner) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    GeneralPaperMeshPrefixInvariant.Good m a.lambda k Qv (block learner (snapshotAt (epochRun shared a k trees) time j)).cdf := by
  dsimp only
  rw [epochRun_selected]
  exact GeneralPaperActualMeshPrefixInvariant.selected_good _ Qv weights Bc Br time ht j learner

theorem prepared_epoch_good {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (learner : Learner) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    GeneralPaperMeshPrefixInvariant.Good m a.lambda k Qv (block learner (snapshotAt (epochRun shared a k trees) time j)).cdf := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_good (GeneralPaperProxyParameters.alphabet m k) k Qv weights Bc Br epoch time ht j learner

end Blotto.GeneralPaperActualMeshQueryPrice
