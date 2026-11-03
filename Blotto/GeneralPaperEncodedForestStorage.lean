import Blotto.GeneralPaperSparseNodeBits

/-! Encoded retained forests combine actual node certificates and counts.
Root arrays and descriptors are included. Old/new forests may coexist;
partial update batches keep the same next-boundary size envelope. -/
namespace Blotto.GeneralPaperEncodedForestStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
open GeneralPaperGlobalNodeQuery
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {m lambda : ℕ} (W : ℕ) (trees : Trees m lambda) : ℕ :=
  (∑ j, (GeneralPaperSparseNodeBits.footprint W (trees.p.read j)+GeneralPaperSparseNodeBits.footprint W (trees.q.read j)+
    GeneralPaperSparseNodeBits.footprint W (trees.lambda.read j)+GeneralPaperSparseNodeBits.footprint W (trees.mu.read j)))+4*m*W+64*W

def profile (W m lambda k Qv : ℕ) : ℕ :=
  4*m*GeneralPaperRetainedForestNodes.perField lambda k (GeneralPaperTrajectoryParameters.prepare lambda k).epochs*
    GeneralPaperSparseNodeBits.perNode W m lambda k Qv+4*m*W+64*W

theorem bounded {m : ℕ} (W Qv k : ℕ) (a : Alphabet) (trees : Trees m a.lambda)
    (hv : Valid a k trees) (hp : Paths a k trees) :
    footprint W trees≤GeneralPaperRetainedForestNodes.total trees*GeneralPaperSparseNodeBits.perNode W m a.lambda k Qv+4*m*W+64*W := by
  have hn (learner : Learner) (j : Fin m) := GeneralPaperSparseNodeBits.bounded W m a.lambda k Qv (node learner trees j)
    (tree_height_bound learner a.lambda) (hv learner j) (hp learner j)
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (f:=fun j => GeneralPaperSparseNodeBits.footprint W (trees.p.read j)+GeneralPaperSparseNodeBits.footprint W (trees.q.read j)+
      GeneralPaperSparseNodeBits.footprint W (trees.lambda.read j)+GeneralPaperSparseNodeBits.footprint W (trees.mu.read j))
    (g:=fun j => (nodes (trees.p.read j)+nodes (trees.q.read j)+nodes (trees.lambda.read j)+nodes (trees.mu.read j))*GeneralPaperSparseNodeBits.perNode W m a.lambda k Qv)
    (by
      intro j _
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hn .p j) (hn .q j)) (hn .lambda j)) (hn .mu j)).trans_eq (by
        dsimp only [node,treeHeight]
        ring))
  rw [←Finset.sum_mul] at hs
  exact Nat.add_le_add_right (Nat.add_le_add_right hs _) _

theorem actual {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    footprint W (treesAt (prepare a k Qv weights Bc Br) a k count)≤profile W m a.lambda k Qv := by
  have hf := bounded W Qv k a _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br count he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br count he)
  have hn := Nat.mul_le_mul_right (GeneralPaperSparseNodeBits.perNode W m a.lambda k Qv)
    (GeneralPaperRetainedForestNodes.total_nodes a k Qv weights Bc Br _ count he)
  exact hf.trans (Nat.add_le_add_right (Nat.add_le_add_right hn _) _)

theorem old_new {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    footprint W (treesAt (prepare a k Qv weights Bc Br) a k count)+footprint W (treesAt (prepare a k Qv weights Bc Br) a k (count+1))≤
      2*profile W m a.lambda k Qv := by
  have hp := actual W k Qv a weights Bc Br count (by omega)
  have hn := actual W k Qv a weights Bc Br (count+1) he
  omega

theorem partial_batch {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count prefixCount : ℕ) (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (j : Fin m) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k count
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    let partialNode := (GeneralPaperIntervalBatch.run shared.powers (treeHeight learner a.lambda) (span learner shared)
      (node learner trees j) ((GeneralPaperCatalogueCellHistory.batchOfState learner state j).take prefixCount)).node
    GeneralPaperSparseNodeBits.footprint W partialNode≤
      GeneralPaperRetainedForestNodes.perField a.lambda k shared.trajectory.epochs*GeneralPaperSparseNodeBits.perNode W m a.lambda k Qv := by
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k count
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  let entries := GeneralPaperCatalogueCellHistory.batchOfState learner state j
  let partialNode := (GeneralPaperIntervalBatch.run shared.powers (treeHeight learner a.lambda) (span learner shared)
    (node learner trees j) (entries.take prefixCount)).node
  have hv := GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br count (by omega : count≤_)
  have hf := GeneralPaperActualForestUpdate.final_cap a k Qv weights Bc Br count he learner j
  have hpv := GeneralPaperIntervalBatchBounds.prefix_valid a.lambda k (treeHeight learner a.lambda) (span learner shared)
    (node learner trees j) entries (span_power learner a k Qv weights Bc Br) (hv learner j) hf prefixCount
  have hpp : PathBound (GeneralPaperPowerPrecision.levelBound a.lambda k) 0 partialNode := by
    intro i hi
    have ht := GeneralPaperIntervalBatchBounds.effect_take_le entries prefixCount i
    have hb := hf i hi
    change GeneralPaperIntervalLevels.levelAt (node learner trees j) i+GeneralPaperIntervalBatch.effect entries i≤
      GeneralPaperPowerPrecision.levelBound a.lambda k at hb
    change 0+GeneralPaperIntervalLevels.levelAt partialNode i≤_
    rw [Nat.zero_add,GeneralPaperIntervalBatch.run_levels shared.powers _ _ _ _ (span_power learner a k Qv weights Bc Br) i hi]
    omega
  have hbits := GeneralPaperSparseNodeBits.bounded W m a.lambda k Qv partialNode (tree_height_bound learner a.lambda) hpv hpp
  have hn := GeneralPaperRetainedForestNodes.partial_batch_nodes a k Qv weights Bc Br count prefixCount learner j
  have hb := Nat.mul_le_mul (Nat.mul_le_mul_right (GeneralPaperBatchCounterPrice.limit k)
    (Nat.mul_le_mul_left 4 (tree_height_bound learner a.lambda))) he
  have hCap : nodes partialNode≤GeneralPaperRetainedForestNodes.perField a.lambda k shared.trajectory.epochs := hn.trans (Nat.add_le_add_left hb 1)
  exact hbits.trans (Nat.mul_le_mul_right _ hCap)

theorem returned {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    footprint W (GeneralPaperGeometricSourceExecution.run bits index model W k Qv a c hc shared count).1.1≤profile W m a.lambda k Qv := by
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data bits index model W k Qv a c hc weights Bc Br count he]
  exact actual W k Qv a weights Bc Br count he

end Blotto.GeneralPaperEncodedForestStorage
