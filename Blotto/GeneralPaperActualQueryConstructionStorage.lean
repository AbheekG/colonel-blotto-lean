import Blotto.GeneralPaperSummaryFamilyStorage
import Blotto.GeneralPaperRankConstructionStorage

/-! Query construction at the actual native source: all four outer summary
buffers, each inner summary/query prefix, and cached-rank fills over the
generated retained summary. Code caps follow from the source's actual tree
height; no source, summary, rank or encoding pass is executed by these proofs. -/
namespace Blotto.GeneralPaperActualQueryConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem epoch_summaries {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (hcount : count≤m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    GeneralPaperSummaryFamilyStorage.buffer bits index primitive W m a.lambda k Qv c hc
        (GeneralPaperQuantileComparison.width a.lambda k) a.lambda trees.p count hcount+
      GeneralPaperSummaryFamilyStorage.buffer bits index primitive W m a.lambda k Qv c hc
        (GeneralPaperQuantileComparison.width a.lambda k) a.lambda trees.q count hcount+
      GeneralPaperSummaryFamilyStorage.buffer bits index primitive W m a.lambda k Qv c hc
        (GeneralPaperQuantileComparison.width a.lambda k) (a.lambda+1) trees.lambda count hcount+
      GeneralPaperSummaryFamilyStorage.buffer bits index primitive W m a.lambda k Qv c hc
        (GeneralPaperQuantileComparison.width a.lambda k) (a.lambda+1) trees.mu count hcount≤
      4*GeneralPaperSummaryFamilyStorage.familyProfile W m k (a.lambda+1) :=
  GeneralPaperSummaryFamilyStorage.four_prefixes bits index primitive W m k Qv _ a c hc _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) count hcount

theorem epoch_inner {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m)
    (count : ℕ) (hcount : count≤c.controls.source.summarySize) (r : Fin c.controls.source.summarySize) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j
    GeneralPaperSummaryConstructionStorage.window model index W c (GeneralPaperQuantileComparison.width a.lambda k)
      (treeHeight learner a.lambda) n count hcount r≤
      GeneralPaperSummaryConstructionStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) :=
  GeneralPaperSummaryConstructionStorage.bounded model index W m a.lambda k Qv _ _ c hc rfl _
    (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j) count hcount r

theorem prepared_inner {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (j : Fin m) (count : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) j
    ∀ hc : count≤ready.2.source.controls.source.summarySize,
    ∀ qr : Fin ready.2.source.controls.source.summarySize,
    GeneralPaperSummaryConstructionStorage.window model index W ready.2.source ready.1.2.wordWidth
      (treeHeight learner a.lambda) n count hc qr≤
      GeneralPaperSummaryConstructionStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  intro hc qr
  exact epoch_inner model index W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br epoch he learner j count hc qr

theorem generated_rank {n : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees)
    (learner : Learner) (j : Fin m) (cuts : FixedArrayTable n ℕ)
    (hCuts : ∀ q,cuts.read q≤2^(treeHeight learner a.lambda))
    (count : ℕ) (hcount : count≤n) (q : Fin n) :
    let arrays := (GeneralPaperFourSummaryArrays.run true index model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    GeneralPaperRankConstructionStorage.window model index W k (summary learner cache j) cuts count hcount q≤
      GeneralPaperRankConstructionStorage.profile model W n k (2^(treeHeight learner a.lambda)) := by
  dsimp only
  apply GeneralPaperRankConstructionStorage.bounded model index W k (2^(treeHeight learner a.lambda)) _ cuts count hcount q hCuts
  intro r
  have hCodes := GeneralPaperSourceRankCache.codes true index model.rat W m k Qv a c hc
    (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp learner j r
  exact hCodes.le.trans_eq (GeneralPaperCatalogueEpochMetadata.width_power learner _)

theorem epoch_rank {n m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (j : Fin m) (cuts : FixedArrayTable n ℕ)
    (hCuts : ∀ q,cuts.read q≤2^(treeHeight learner a.lambda))
    (count : ℕ) (hcount : count≤n) (q : Fin n) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true index model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    GeneralPaperRankConstructionStorage.window model index W k (summary learner cache j) cuts count hcount q≤
      GeneralPaperRankConstructionStorage.profile model W n k (2^(treeHeight learner a.lambda)) :=
  generated_rank model index W m k Qv a c hc _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) learner j cuts hCuts count hcount q

end Blotto.GeneralPaperActualQueryConstructionStorage
