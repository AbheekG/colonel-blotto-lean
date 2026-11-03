import Blotto.GeneralPaperQuantileSearchPrice

/-! Every retained epoch forest and the actual returned preparation cache
discharge the root-search premises. State expressions identify existing
forests; they do not execute another epoch or preparation inside a search.
-/
namespace Blotto.GeneralPaperActualQuantileSearch
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem epoch_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv target : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (field : Fin m)
    (hTarget : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) field
    (GeneralPaperQuantileSearchExecution.run true primitive W c (GeneralPaperQuantileComparison.width a.lambda k)
      target (treeHeight learner a.lambda) n).2≤
      GeneralPaperQuantileSearchPrice.profile primitive W m a.lambda k Qv (treeHeight learner a.lambda) := by
  exact GeneralPaperQuantileSearchPrice.bit_work primitive hMono W m a.lambda k Qv _ target _ c hc rfl _ hTarget
    (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner field)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner field)

theorem epoch_bracket {m : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W k Qv target : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (field : Fin m)
    (hTarget : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) field
    let x := (GeneralPaperQuantileSearchExecution.run bits primitive W c (GeneralPaperQuantileComparison.width a.lambda k)
      target (treeHeight learner a.lambda) n).1.location
    GeneralPaperQuantileSearch.cdf k n x≤(target:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+GeneralPaperNormalizedMassError.delta k ∧
      (target:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-GeneralPaperNormalizedMassError.delta k≤GeneralPaperQuantileSearch.cdf k n (x+1) := by
  exact GeneralPaperQuantileSearchPrice.bracket bits primitive W m a.lambda k Qv _ target _ c hc rfl _ hTarget
    (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner field)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner field)

theorem prepared_work {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (field : Fin m) (hTarget : target≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) field
    (GeneralPaperQuantileSearchExecution.run true model.rat W ready.2.source ready.1.2.wordWidth target (treeHeight learner a.lambda) n).2≤
      GeneralPaperQuantileSearchPrice.profile model.rat W m a.lambda k Qv (treeHeight learner a.lambda) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model.rat model.monotone W k Qv target (GeneralPaperProxyParameters.alphabet m k) _ rfl
    weights Bc Br epoch he learner field hTarget

theorem prepared_arithmetic_work {m : ℕ} (k Qv target : ℕ) (b : ℝ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (field : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) field
    (GeneralPaperQuantileSearchExecution.run false (fun _ => 1) 1 ready.2.source ready.1.2.wordWidth target (treeHeight learner a.lambda) n).2≤
      16777216*(treeHeight learner a.lambda+1)*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)^2 := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  exact GeneralPaperQuantileSearchPrice.arithmetic_work m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ target _ _ rfl rfl _

theorem prepared_same_data {m : ℕ} (model : RationalCostModel) (W k Qv target : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (field : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) field
    (GeneralPaperQuantileSearchExecution.run true model.rat W ready.2.source ready.1.2.wordWidth target (treeHeight learner a.lambda) n).1=
      (GeneralPaperQuantileSearchExecution.run false (fun _ => 1) 1 ready.2.source ready.1.2.wordWidth target (treeHeight learner a.lambda) n).1 := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  apply GeneralPaperQuantileSearchPrice.same_data model.rat W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ target _ _ rfl _
  · exact tree_height_bound learner _
  · exact GeneralPaperCatalogueOuterValidity.trees_valid _ _ _ _ _ _ epoch he learner field
  · exact GeneralPaperCatalogueOuterValidity.trees_paths _ _ _ _ _ _ epoch he learner field

end Blotto.GeneralPaperActualQuantileSearch
