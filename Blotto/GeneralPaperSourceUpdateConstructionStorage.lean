import Blotto.GeneralPaperActualUpdateConstructionStorage

/-! Complete native field/round constructors join the full reached source,
selector/root/profit/streaming-DP and query callback context. Actual source
plans derive all count/code premises; prepared callers and a retained first
trajectory preserve the same join. Releases/global W remain separate. -/
namespace Blotto.GeneralPaperSourceUpdateConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem epoch_round {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (count : ℕ) (hc : count≤m) (j : Fin m) (innerCount : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    GeneralPaperActualUpdateConstructionStorage.roundWindow model W Qv cache weights Bc Br time count hc j innerCount≤
      GeneralPaperActualUpdateConstructionStorage.roundProfile model W m a.lambda k Qv :=
  GeneralPaperActualUpdateConstructionStorage.round_selected model W Qv _
    (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) weights Bc Br time ht count hc j innerCount

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  GeneralPaperSourceGridCallbackStorage.window model W k Qv a shared weights Bc Br epoch time j i count copied rowCount hc hr left right+
    GeneralPaperActualUpdateConstructionStorage.roundWindow model W Qv cache weights Bc Br time rowCount hr j innerCount

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperSourceGridCallbackStorage.profile model W k Qv a weights Bc Br+
    GeneralPaperActualUpdateConstructionStorage.roundProfile model W m a.lambda k Qv

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) :
    window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperSourceGridCallbackStorage.actual model W k Qv a weights Bc Br hWeights epoch time he (by omega)
    j i count copied rowCount hc hr left right) (epoch_round model W k Qv a weights Bc Br epoch time ht rowCount hr j innerCount)

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) (innerCount : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    ∀ left right : Fin (GeneralPaperProfitParameters.prepare m ready.1.1.1.2.lambda k Qv).grid.size,
    window model W k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      profile model W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  intro left right
  exact actual model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht
    j i count copied rowCount hc hr left right innerCount

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right innerCount)

end Blotto.GeneralPaperSourceUpdateConstructionStorage
