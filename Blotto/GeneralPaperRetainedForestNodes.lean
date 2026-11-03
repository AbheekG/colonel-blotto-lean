import Blotto.GeneralPaperGeometricSourcePrice

/-! Counts of the actual sparse forest nodes and every partial batch.
These are erased size observers, not storage censuses run by the algorithm.
No exponential code interval is enumerated. -/
namespace Blotto.GeneralPaperRetainedForestNodes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
open GeneralPaperCatalogueEpochCache
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem batch_length {m k : ℕ} {cache : Cache m k} (learner : Learner) (state : State cache) (j : Fin m) :
    (GeneralPaperCatalogueCellHistory.batchOfState learner state j).length≤GeneralPaperBatchCounterPrice.limit k := by
  rw [GeneralPaperCatalogueCellHistory.batchOfState,GeneralPaperEpochCellInstructions.build_length]
  exact GeneralPaperActualEpochInstructions.cell_count learner cache j

theorem updated_nodes {m k : ℕ} {cache : Cache m k} (a : Alphabet) (Qv : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (trees : Trees m a.lambda)
    (state : State cache) (learner : Learner) (j : Fin m) :
    nodes (node learner (GeneralPaperCatalogueForestUpdate.apply (prepare a k Qv weights Bc Br) trees state) j)≤
      nodes (node learner trees j)+4*(treeHeight learner a.lambda)*GeneralPaperBatchCounterPrice.limit k := by
  rw [GeneralPaperCatalogueForestUpdate.node_apply]
  have hs : 0<span learner (prepare a k Qv weights Bc Br) := by rw [span_power]; positivity
  have hn := GeneralPaperIntervalBatchBounds.node_bound (prepare a k Qv weights Bc Br).powers
    (treeHeight learner a.lambda) (span learner (prepare a k Qv weights Bc Br)) (node learner trees j)
    (GeneralPaperCatalogueCellHistory.batchOfState learner state j) hs
  exact hn.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (batch_length learner state j)) _)

theorem trees_nodes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (learner : Learner) (j : Fin m) :
    nodes (node learner (treesAt (prepare a k Qv weights Bc Br) a k count) j)≤
      1+4*(treeHeight learner a.lambda)*GeneralPaperBatchCounterPrice.limit k*count := by
  induction count with
  | zero => cases learner <;> simp only [trees_initial,node,GeneralPaperCatalogueTreeCache.initial,FixedArrayTable.read_ofFn,nodes,Nat.mul_zero,Nat.add_zero,le_refl]
  | succ count ih =>
    rw [trees_step,epoch_trees]
    have hu := updated_nodes a Qv weights Bc Br (treesAt (prepare a k Qv weights Bc Br) a k count)
      (GeneralPaperCatalogueEpochRun.stateAt (epochRun (prepare a k Qv weights Bc Br) a k
        (treesAt (prepare a k Qv weights Bc Br) a k count)) (prepare a k Qv weights Bc Br).trajectory.period) learner j
    nlinarith only [ih,hu]

theorem partial_batch_nodes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count prefixCount : ℕ) (learner : Learner) (j : Fin m) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k count
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    nodes (GeneralPaperIntervalBatch.run shared.powers (treeHeight learner a.lambda) (span learner shared)
      (node learner trees j) ((GeneralPaperCatalogueCellHistory.batchOfState learner state j).take prefixCount)).node≤
      1+4*(treeHeight learner a.lambda)*GeneralPaperBatchCounterPrice.limit k*(count+1) := by
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k count
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  have hs : 0<span learner shared := by rw [span_power]; positivity
  have hp := GeneralPaperIntervalBatchBounds.prefix_nodes shared.powers (treeHeight learner a.lambda) (span learner shared)
    (node learner trees j) (GeneralPaperCatalogueCellHistory.batchOfState learner state j) hs prefixCount
  have hn := trees_nodes a k Qv weights Bc Br count learner j
  have hl := Nat.mul_le_mul_left (4*(treeHeight learner a.lambda)) (batch_length learner state j)
  dsimp only
  nlinarith only [hp,hn,hl]

def perField (lambda k epochs : ℕ) : ℕ := 1+4*(lambda+1)*GeneralPaperBatchCounterPrice.limit k*epochs

theorem uniform_nodes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochs count : ℕ) (he : count≤epochs) (learner : Learner) (j : Fin m) :
    nodes (node learner (treesAt (prepare a k Qv weights Bc Br) a k count) j)≤perField a.lambda k epochs := by
  have h := trees_nodes a k Qv weights Bc Br count learner j
  have hb := Nat.mul_le_mul
    (Nat.mul_le_mul_right (GeneralPaperBatchCounterPrice.limit k) (Nat.mul_le_mul_left 4 (tree_height_bound learner a.lambda))) he
  exact h.trans (Nat.add_le_add_left hb 1)

def total {m lambda : ℕ} (trees : Trees m lambda) : ℕ :=
  ∑ j, (nodes (trees.p.read j)+nodes (trees.q.read j)+nodes (trees.lambda.read j)+nodes (trees.mu.read j))

theorem total_nodes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochs count : ℕ) (he : count≤epochs) :
    total (treesAt (prepare a k Qv weights Bc Br) a k count)≤4*m*perField a.lambda k epochs := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (f:=fun j =>
      nodes ((treesAt (prepare a k Qv weights Bc Br) a k count).p.read j)+
      nodes ((treesAt (prepare a k Qv weights Bc Br) a k count).q.read j)+
      nodes ((treesAt (prepare a k Qv weights Bc Br) a k count).lambda.read j)+
      nodes ((treesAt (prepare a k Qv weights Bc Br) a k count).mu.read j))
    (g:=fun _ : Fin m => 4*perField a.lambda k epochs) (by
      intro j _
      have hp := uniform_nodes a k Qv weights Bc Br epochs count he .p j
      have hq := uniform_nodes a k Qv weights Bc Br epochs count he .q j
      have hl := uniform_nodes a k Qv weights Bc Br epochs count he .lambda j
      have hu := uniform_nodes a k Qv weights Bc Br epochs count he .mu j
      calc
        _≤perField a.lambda k epochs+perField a.lambda k epochs+perField a.lambda k epochs+perField a.lambda k epochs :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hq) hl) hu
        _=4*perField a.lambda k epochs := by ring)
  simpa only [total,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc,Nat.mul_left_comm] using h

theorem old_new_nodes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochs count : ℕ) (he : count+1≤epochs) :
    total (treesAt (prepare a k Qv weights Bc Br) a k count)+total (treesAt (prepare a k Qv weights Bc Br) a k (count+1))≤
      8*m*perField a.lambda k epochs := by
  have hp := total_nodes a k Qv weights Bc Br epochs count (by omega)
  have hn := total_nodes a k Qv weights Bc Br epochs (count+1) he
  nlinarith only [hp,hn]

theorem returned_nodes {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    total (GeneralPaperGeometricSourceExecution.run bits index model W k Qv a c hc shared count).1.1≤
      4*m*perField a.lambda k shared.trajectory.epochs := by
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data bits index model W k Qv a c hc weights Bc Br count he]
  exact total_nodes a k Qv weights Bc Br _ count he

end Blotto.GeneralPaperRetainedForestNodes
