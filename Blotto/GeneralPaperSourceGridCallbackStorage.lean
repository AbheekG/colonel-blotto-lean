import Blotto.GeneralPaperActualQueryCallbackStorage

/-! Active grid leaf and merge callback scratch joins reached native
source/root/DP residents and both option callbacks. Grid operands come from
the actual prepared grid and native profit fields. Only one active callback
is counted per selector; no sum over table cells or uniform resource-height
charge at every DP level is introduced. -/
namespace Blotto.GeneralPaperSourceGridCallbackStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def gridWindow {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ)
    (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (left right : Fin (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv).grid.size) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let candidate := (GeneralPaperNativeProfitLeafExecution.run true (fun w => w) model.rat W T (weights.read j)
    (before.read j).lambda.cdf (cache.candidate.cached.read j)).1
  let response := (GeneralPaperNativeProfitLeafExecution.run true (fun w => w) model.rat W T (weights.read j)
    (before.read j).mu.cdf (cache.response.cached.read j)).1
  GeneralPaperProfitGridQueryStorage.leafWindow model W p.grid (candidate.read i).1+
    GeneralPaperProfitGridQueryStorage.leafWindow model W p.grid (response.read i).1+
    GeneralPaperProfitGridQueryStorage.mergeWindow model W p.grid (p.grid.numerators.read left+p.grid.numerators.read right)

def gridProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  3*GeneralPaperProfitGridQueryStorage.compact model W (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.depth
    (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)

theorem both_grid {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (left right : Fin (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv).grid.size) :
    gridWindow model W Qv cache weights (beforeAt (selected cache Qv weights Bc Br) time) j i left right≤
      gridProfile model W m cache.alphabet.lambda k Qv := by
  let p := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let before := beforeAt (selected cache Qv weights Bc Br) time
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := GeneralPaperActualProfitGridQueryStorage.ready_leaf model W Qv T p cache.candidate (by rw [hca]) weights
    (FixedArrayTable.ofFn (fun a => (before.read a).lambda.cdf)) j i (by rw [hca]) hWeights (by
      rw [hca,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
  have hr := GeneralPaperActualProfitGridQueryStorage.ready_leaf model W Qv T p cache.response (by rw [hra]) weights
    (FixedArrayTable.ofFn (fun a => (before.read a).mu.cdf)) j i (by rw [hra]) hWeights (by
      rw [hra,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)
  rw [hca] at hc
  rw [hra] at hr
  have hm := GeneralPaperActualProfitGridQueryStorage.merge model W m cache.alphabet.lambda k Qv p.parameters rfl p.grid rfl left right
  simp only [FixedArrayTable.read_ofFn] at hc hr
  exact (Nat.add_le_add (Nat.add_le_add hc hr) hm).trans_eq (by unfold gridProfile; ring)

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  GeneralPaperActualQueryCallbackStorage.window model W k Qv a shared weights Bc Br epoch time j i count copied rowCount hc hr+
    gridWindow model W Qv cache weights (beforeAt current time) j i left right

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperActualQueryCallbackStorage.profile model W k Qv a weights Bc Br+gridProfile model W m a.lambda k Qv

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) :
    window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right≤
      profile model W k Qv a weights Bc Br := by
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  have hbase := GeneralPaperActualQueryCallbackStorage.actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr
  have hgrid := both_grid model W Qv cache weights Bc Br hWeights time ht j i left right
  exact Nat.add_le_add hbase hgrid

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    ∀ left right : Fin (GeneralPaperProfitParameters.prepare m ready.1.1.1.2.lambda k Qv).grid.size,
    window model W k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time j i count copied rowCount hc hr left right≤
      profile model W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  intro left right
  exact actual model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right)

end Blotto.GeneralPaperSourceGridCallbackStorage
