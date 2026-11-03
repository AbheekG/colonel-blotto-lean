import Blotto.GeneralPaperBatchTraversalStorage
import Blotto.GeneralPaperActualTraversalStorage

/-! Actual stored epoch cell arrays supply increment caps for all native
range instructions, including empty cells. The complete effect invariant
supplies every successive update state. No list/level validation executes. -/
namespace Blotto.GeneralPaperActualBatchStorage
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueCellHistory GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperCatalogueTreeCache
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem resize_bound {n p : ℕ} (h : n=p) (values : FixedArrayTable n ℕ) (G : ℕ)
    (hb : ∀ r,values.read r≤G) : ∀ r,(GeneralPaperRowPrefix.resize h values).read r≤G := by
  cases h
  exact hb

theorem cell_bound {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) (G : ℕ)
    (hb : GeneralPaperEpochFieldState.Bounded state G) : ∀ r,(cellArray learner state).read r≤G := by
  cases learner with
  | p => exact hb.2.2.2.2.1
  | q => exact hb.2.2.2.2.2.1
  | lambda => exact hb.2.2.2.2.2.2.1
  | mu => exact hb.2.2.2.2.2.2.2

theorem good {m k : ℕ} {cache : Cache m k} (learner : Learner) (state : State cache) (j : Fin m)
    (hb : GeneralPaperEpochFieldState.Bounded (state.fields.read j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k)) :
    GeneralPaperBatchTraversalStorage.Good cache.alphabet.lambda k (batchOfState learner state j) := by
  intro e he
  have hEnd := GeneralPaperActualEpochInstructions.endpoints false (fun _ => 1) 1 learner state j e
    (by rw [GeneralPaperActualEpochInstructions.data]; exact he)
  refine ⟨hEnd.1,hEnd.2,?_⟩
  change e∈List.ofFn _ at he
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp he
  rw [←hr]
  exact resize_bound _ _ _ (cell_bound learner (state.fields.read j) _ hb) r

theorem selected_good {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (learner : Learner) (j : Fin m) :
    GeneralPaperBatchTraversalStorage.Good cache.alphabet.lambda k
      (batchOfState learner (stateAt (selected cache Qv weights Bc Br) time) j) :=
  good learner _ j (selected_cap cache Qv weights Bc Br time ht j)

theorem node_batch {m k : ℕ} {cache : Cache m k} (model : RationalCostModel) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (learner : Learner) (state : State cache) (j : Fin m) (height : ℕ) (n : Node height) (span : ℚ)
    (hs : span=(2:ℚ)^height) (hh : height≤cache.alphabet.lambda+1) (hv : Valid cache.alphabet.lambda k n)
    (hb : GeneralPaperEpochFieldState.Bounded (state.fields.read j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k))
    (hf : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect (batchOfState learner state j) i≤
      GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    GeneralPaperBatchTraversalStorage.peak model W c height span n (batchOfState learner state j)≤
      (GeneralPaperBatchCounterPrice.limit k+1)*GeneralPaperBatchTraversalStorage.frameProfile model W m cache.alphabet.lambda k Qv+
        GeneralPaperRangeQueryStorage.profile model W m cache.alphabet.lambda k Qv height := by
  have hn : (batchOfState learner state j).length≤GeneralPaperBatchCounterPrice.limit k := by
    have h := GeneralPaperActualEpochInstructions.length false (fun _ => 1) 1 learner state j
    rw [GeneralPaperActualEpochInstructions.data] at h
    exact h
  exact (GeneralPaperBatchTraversalStorage.bounded model W m cache.alphabet.lambda k Qv height c hc span n
    (batchOfState learner state j) hs hh hn (good learner state j hb) hv hf).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1)) _)

theorem epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let state := stateAt (GeneralPaperCatalogueShared.epochRun shared a k trees) shared.trajectory.period
    GeneralPaperBatchTraversalStorage.peak model W c (treeHeight learner a.lambda)
      (GeneralPaperCatalogueShared.span learner shared) (node learner trees j) (batchOfState learner state j)≤
      (GeneralPaperBatchCounterPrice.limit k+1)*GeneralPaperBatchTraversalStorage.frameProfile model W m a.lambda k Qv+
        GeneralPaperRangeQueryStorage.profile model W m a.lambda k Qv (treeHeight learner a.lambda) := by
  exact node_batch model W Qv c hc learner _ j _ _ _
    (GeneralPaperCatalogueShared.span_power learner a k Qv weights Bc Br)
    (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega) learner j)
    (selected_cap _ Qv weights Bc Br _ (Nat.le_refl _) j)
    (GeneralPaperActualForestUpdate.final_cap a k Qv weights Bc Br epoch he learner j)

end Blotto.GeneralPaperActualBatchStorage
