import Blotto.GeneralPaperQuantileQueryStorage
import Blotto.GeneralPaperRangeQueryStorage
import Blotto.GeneralPaperSharedResidentStorage
import Blotto.GeneralPaperStreamingQueryEnvelope

/-! Whole-query storage at the actual retained epoch forest and prepared
source return. Source/root quotient classifiers share the existing streaming
CF bound. Resident source data and a first completed trajectory may coexist.
Initialization, other callback stacks and the final global W remain open. -/
namespace Blotto.GeneralPaperActualTraversalStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem epoch_quantile {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (field : Fin m) (ht : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) field
    GeneralPaperQuantileQueryStorage.window model W c (GeneralPaperQuantileComparison.width a.lambda k)
      target (treeHeight learner a.lambda) n≤
      GeneralPaperQuantileQueryStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) :=
  GeneralPaperQuantileQueryStorage.bounded model W m a.lambda k Qv _ target _ c hc _ rfl ht
    (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner field)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner field)

theorem prepared_quantile {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (field : Fin m) (ht : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) field
    GeneralPaperQuantileQueryStorage.window model W ready.2.source ready.1.2.wordWidth
      target (treeHeight learner a.lambda) n≤
      GeneralPaperQuantileQueryStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_quantile model W k Qv target (GeneralPaperProxyParameters.alphabet m k) _ rfl
    weights Bc Br epoch he learner field ht

theorem classifier_pair (model : RationalCostModel) (m k sourceCode rootCode : ℕ)
    (sourceClosed rootClosed : Bool) (hm : 0<m)
    (hs : sourceCode<(GeneralPaperProxyParameters.alphabet m k).C)
    (hr : rootCode<(GeneralPaperProxyParameters.prepare m k).Qg) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let r := GeneralPaperProxyParameters.prepare m k
    max (GeneralPaperStreamingQuerySpace.peak model (GeneralPaperPrecallControlWord.word m k)
      sourceClosed a.D a.C sourceCode a.lambda)
      (GeneralPaperStreamingQuerySpace.peak model (GeneralPaperPrecallControlWord.word m k)
        rootClosed r.H r.Qg rootCode (r.gridBits+3))≤
      1024*model.rat (GeneralPaperStreamingQueryEnvelope.width m k) :=
  max_le (GeneralPaperStreamingQueryEnvelope.source_space model m k sourceCode sourceClosed hm hs)
    (GeneralPaperStreamingQueryEnvelope.root_space model m k rootCode rootClosed hm hr)

theorem resident_quantile {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (htime : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (learner : Learner) (field : Fin m) (ht : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let shared := prepare a k Qv weights Bc Br
    let n := node learner (treesAt shared a k epoch) field
    GeneralPaperEncodedSharedSource.footprint W shared+
      GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time+
      GeneralPaperQuantileQueryStorage.window model W c shared.wordWidth target (treeHeight learner a.lambda) n≤
    GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+
      GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv+
      GeneralPaperQuantileQueryStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) :=
  Nat.add_le_add (GeneralPaperSharedResidentStorage.actual W k Qv a weights Bc Br epoch time he htime)
    (epoch_quantile model W k Qv target a c hc weights Bc Br epoch he learner field ht)

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (htime : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (learner : Learner) (field : Fin m) (ht : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let first := prepare a k Qv weights firstBc firstBr
    let shared := prepare a k Qv weights Bc Br
    let n := node learner (treesAt shared a k epoch) field
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2+
      (GeneralPaperEncodedSharedSource.footprint W shared+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time+
        GeneralPaperQuantileQueryStorage.window model W c shared.wordWidth target (treeHeight learner a.lambda) n)≤
    GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
      (GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+
        GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv+
        GeneralPaperQuantileQueryStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda)) :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (resident_quantile model W k Qv target a c hc weights Bc Br epoch time he htime learner field ht)

end Blotto.GeneralPaperActualTraversalStorage
