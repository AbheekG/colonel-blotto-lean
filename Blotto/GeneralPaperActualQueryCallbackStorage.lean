import Blotto.GeneralPaperNativeProfitLeafStorage
import Blotto.GeneralPaperActualRootProfitStorage

/-! Reached native epoch prefixes discharge query invariants. Both actual
profit-option children join the complete source/root/DP resident context.
This counts one active callback per selector, never a sum over DP cells.
Literal input budget words and the global reference word remain explicit. -/
namespace Blotto.GeneralPaperActualQueryCallbackStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem epoch_counts {m n : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (cdfLearner tailLearner : Learner) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    let shared := prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := epochRun shared a k trees
    GeneralPaperMeshPairStorage.countsWindow model W (GeneralPaperSourceParameters.prepare k).meshDenominator
      (block cdfLearner (snapshotAt current time j)).cdf (block tailLearner (snapshotAt current time j)).cdf plan q≤
      GeneralPaperMeshPairStorage.countsProfile model W m a.lambda k Qv n :=
  GeneralPaperMeshPairStorage.counts_bounded model W m a.lambda Qv _ _ _ plan q rfl
    (GeneralPaperActualMeshQueryPrice.epoch_good a k Qv weights Bc Br epoch time ht j cdfLearner)
    (GeneralPaperActualMeshQueryPrice.epoch_good a k Qv weights Bc Br epoch time ht j tailLearner)

theorem prepared_counts {m n : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (cdfLearner tailLearner : Learner) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt ready.1.2 a k epoch
    let current := epochRun ready.1.2 a k trees
    GeneralPaperMeshPairStorage.countsWindow model W (GeneralPaperSourceParameters.prepare k).meshDenominator
      (block cdfLearner (snapshotAt current time j)).cdf (block tailLearner (snapshotAt current time j)).cdf plan q≤
      GeneralPaperMeshPairStorage.countsProfile model W m a.lambda k Qv n := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_counts model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br epoch time ht j cdfLearner tailLearner plan q

def optionWindow {m k : ℕ} (model : RationalCostModel) (W : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ)
    (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) : ℕ :=
  GeneralPaperNativeProfitLeafStorage.elementWindow model W cache.candidate (weights.read j) (before.read j).lambda.cdf j i+
    GeneralPaperNativeProfitLeafStorage.elementWindow model W cache.response (weights.read j) (before.read j).mu.cdf j i

theorem both_options {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    optionWindow model W cache weights (beforeAt (selected cache Qv weights Bc Br) time) j i≤
      2*GeneralPaperNativeProfitLeafStorage.elementProfile model W m cache.alphabet.lambda k Qv := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hw := GeneralPaperEncodedProfitInput.weight_le weights Qv hWeights j
  have hp := GeneralPaperNativeProfitLeafStorage.element_bounded model W Qv cache.candidate (weights.read j)
    ((beforeAt (selected cache Qv weights Bc Br) time).read j).lambda.cdf j i hw (by
      rw [hca]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
  have hr := GeneralPaperNativeProfitLeafStorage.element_bounded model W Qv cache.response (weights.read j)
    ((beforeAt (selected cache Qv weights Bc Br) time).read j).mu.cdf j i hw (by
      rw [hra]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)
  rw [hca] at hp
  rw [hra] at hr
  exact (Nat.add_le_add hp hr).trans_eq (by ring)

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  GeneralPaperActualRootProfitStorage.window true (fun w => w) model.rat W W k Qv a shared weights Bc Br epoch time j i count copied rowCount hc hr+
    optionWindow model W cache weights (beforeAt current time) j i

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperActualRootProfitStorage.profile W k Qv a weights Bc Br+
    2*GeneralPaperNativeProfitLeafStorage.elementProfile model W m a.lambda k Qv

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr≤
      profile model W k Qv a weights Bc Br := by
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  have hbase := GeneralPaperActualRootProfitStorage.actual true (fun w => w) model.rat W W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr
  have hoptions := both_options model W Qv cache weights Bc Br hWeights time ht j i
  exact Nat.add_le_add hbase hoptions

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    window model W k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time j i count copied rowCount hc hr≤
      profile model W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact actual model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr)

end Blotto.GeneralPaperActualQueryCallbackStorage
