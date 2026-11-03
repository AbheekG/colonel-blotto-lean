import Blotto.GeneralPaperMeshPairPrice

/-! Actual reached snapshots supply both prefix invariants for four-count
loss queries and the signed-tail query used by the row selectors. Returned
source caches supply the same callers without preparing any object again.
-/
namespace Blotto.GeneralPaperActualMeshPairPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem counts_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m)
    (cdfLearner tailLearner : Learner) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    let snapshot := snapshotAt (selected cache Qv weights Bc Br) time j
    let cp := (block cdfLearner snapshot).cdf
    let tp := (block tailLearner snapshot).cdf
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperMeshPairExecution.counts true model.rat W mesh cp tp plan q).2≤
      GeneralPaperMeshPairPrice.countsProfile model.rat W m cache.alphabet.lambda k Qv ∧
    (GeneralPaperMeshPairExecution.counts false (fun _ => 1) 1 mesh cp tp plan q).2≤
      GeneralPaperMeshPairPrice.countsArithmeticProfile k := by
  have hCDF := GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j cdfLearner
  have hTail := GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j tailLearner
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  exact ⟨GeneralPaperMeshPairPrice.counts_bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _ _ plan q hm hCDF hTail,
    GeneralPaperMeshPairPrice.counts_arithmetic_work _ _ _ plan q⟩

theorem tails_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m)
    (learner : Learner) (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n) :
    let prefixes := (block learner (snapshotAt (selected cache Qv weights Bc Br) time j)).cdf
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperMeshPairExecution.tails true model.rat W mesh prefixes plan q).2≤
      GeneralPaperMeshPairPrice.tailsProfile model.rat W m cache.alphabet.lambda k Qv ∧
    (GeneralPaperMeshPairExecution.tails false (fun _ => 1) 1 mesh prefixes plan q).2≤
      GeneralPaperMeshPairPrice.tailsArithmeticProfile k := by
  have hGood := GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  exact ⟨GeneralPaperMeshPairPrice.tails_bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _ plan q hm hGood,
    GeneralPaperMeshPairPrice.tails_arithmetic_work _ _ plan q⟩

theorem prepared_counts_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) (j : Fin m)
    (cdfLearner tailLearner : Learner) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let snapshot := snapshotAt (epochRun shared a k trees) time j
    let cp := (block cdfLearner snapshot).cdf
    let tp := (block tailLearner snapshot).cdf
    let mesh := ready.2.source.controls.source.meshDenominator
    (GeneralPaperMeshPairExecution.counts true model.rat W mesh cp tp plan q).2≤
      GeneralPaperMeshPairPrice.countsProfile model.rat W m a.lambda k Qv ∧
    (GeneralPaperMeshPairExecution.counts false (fun _ => 1) 1 mesh cp tp plan q).2≤
      GeneralPaperMeshPairPrice.countsArithmeticProfile k := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data,epochRun_selected]
  exact counts_work model W Qv _ _ rfl weights Bc Br time ht j cdfLearner tailLearner plan q

theorem prepared_tails_work {m n k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) (j : Fin m)
    (learner : Learner) (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let prefixes := (block learner (snapshotAt (epochRun shared a k trees) time j)).cdf
    let mesh := ready.2.source.controls.source.meshDenominator
    (GeneralPaperMeshPairExecution.tails true model.rat W mesh prefixes plan q).2≤
      GeneralPaperMeshPairPrice.tailsProfile model.rat W m a.lambda k Qv ∧
    (GeneralPaperMeshPairExecution.tails false (fun _ => 1) 1 mesh prefixes plan q).2≤
      GeneralPaperMeshPairPrice.tailsArithmeticProfile k := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data,epochRun_selected]
  exact tails_work model W Qv _ _ rfl weights Bc Br time ht j learner plan q

end Blotto.GeneralPaperActualMeshPairPrice
