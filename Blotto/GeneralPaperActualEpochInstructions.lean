import Blotto.GeneralPaperBatchUpdateBitPrice

/-! Native retained epoch plans supply instruction counts and endpoint caps
for all four learners. Construction reads the final level arrays, preserves
native batches and introduces no simulation, level-validation or count pass.
-/
namespace Blotto.GeneralPaperActualEpochInstructions
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueCellHistory GeneralPaperCatalogueEpochMetadata
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem cell_count {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m) :
    (partition learner (cache.plans.read j)).count≤GeneralPaperBatchCounterPrice.limit k := by
  cases learner with
  | p =>
    rw [partition,GeneralPaperCatalogueEpochCache.plan_read]
    exact (GeneralPaperUnsignedPartition.count_bound (8*cache.alphabet.C) (cache.q.read j) (cache.lambda.read j)
      (cache.candidate.data.codes.read j)).trans (by unfold GeneralPaperBatchCounterPrice.limit; omega)
  | q =>
    rw [partition,GeneralPaperCatalogueEpochCache.plan_read]
    exact (GeneralPaperUnsignedPartition.count_bound (8*cache.alphabet.C) (cache.p.read j) (cache.mu.read j)
      (cache.response.data.codes.read j)).trans (by unfold GeneralPaperBatchCounterPrice.limit; omega)
  | lambda =>
    rw [partition,GeneralPaperCatalogueEpochCache.plan_read]
    exact (GeneralPaperSignedPartition.count_bound (8*cache.alphabet.C) (cache.p.read j)
      (cache.candidate.data.codes.read j)).trans (by unfold GeneralPaperBatchCounterPrice.limit; omega)
  | mu =>
    rw [partition,GeneralPaperCatalogueEpochCache.plan_read]
    exact (GeneralPaperSignedPartition.count_bound (8*cache.alphabet.C) (cache.q.read j)
      (cache.response.data.codes.read j)).trans (by unfold GeneralPaperBatchCounterPrice.limit; omega)

theorem partition_representation {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m) :
    ∃ points : List ℕ,partition learner (cache.plans.read j)=GeneralPaperPreparedPartition.build (width learner cache) points := by
  cases learner <;> rw [partition,GeneralPaperCatalogueEpochCache.plan_read] <;> exact ⟨_,rfl⟩

theorem bounds_of_build (U : ℕ) (points : List ℕ) (part : GeneralPaperPreparedPartition.Prepared)
    (hPart : part=GeneralPaperPreparedPartition.build U points) (r : Fin part.count) :
    (part.intervals.read r).1≤U ∧ (part.intervals.read r).2≤U := by
  subst part
  change Fin (GeneralPaperPreparedPartition.build U points).count at r
  rw [GeneralPaperPreparedPartition.intervals_eq,GeneralPaperBoundaryCells.read_cells]
  exact ⟨GeneralPaperSortedBreakpoints.ordered_bound U points _ (GeneralPaperPreparedPartition.boundary_member U points r.castSucc),
    GeneralPaperSortedBreakpoints.ordered_bound U points _ (GeneralPaperPreparedPartition.boundary_member U points r.succ)⟩

theorem cell_bounds {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m)
    (r : Fin (partition learner (cache.plans.read j)).count) :
    ((partition learner (cache.plans.read j)).intervals.read r).1≤width learner cache ∧
    ((partition learner (cache.plans.read j)).intervals.read r).2≤width learner cache := by
  obtain ⟨points,hp⟩ := partition_representation learner cache j
  exact bounds_of_build (width learner cache) points _ hp r

def run {m k : ℕ} {cache : Cache m k} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (learner : Learner) (state : State cache) (j : Fin m) : List GeneralPaperIntervalBatch.Instruction × ℕ :=
  GeneralPaperCellInstructionPrice.run bits index W (partition learner (cache.plans.read j)).intervals (levelsOfState learner state j)

theorem data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (learner : Learner) (state : State cache) (j : Fin m) :
    (run bits index W learner state j).1=GeneralPaperCatalogueCellHistory.batchOfState learner state j :=
  GeneralPaperCellInstructionPrice.data bits index W _ _

theorem length {m k : ℕ} {cache : Cache m k} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (learner : Learner) (state : State cache) (j : Fin m) :
    (run bits index W learner state j).1.length≤GeneralPaperBatchCounterPrice.limit k := by
  rw [data,GeneralPaperCatalogueCellHistory.batchOfState,GeneralPaperEpochCellInstructions.build_length]
  exact cell_count learner cache j

theorem endpoints {m k : ℕ} {cache : Cache m k} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (learner : Learner) (state : State cache) (j : Fin m) (entry : GeneralPaperIntervalBatch.Instruction)
    (he : entry∈(run bits index W learner state j).1) :
    entry.lo≤2^(cache.alphabet.lambda+1) ∧ entry.hi≤2^(cache.alphabet.lambda+1) := by
  rw [data] at he
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp he
  rw [←hr]
  have hb := cell_bounds learner cache j r
  have hw : width learner cache≤2^(cache.alphabet.lambda+1) := by
    rw [width_power]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (height_bound learner cache)
  exact ⟨hb.1.trans hw,hb.2.trans hw⟩

theorem profile_mono (W n N : ℕ) (hN : n≤N) : GeneralPaperCellInstructionPrice.profile W n≤GeneralPaperCellInstructionPrice.profile W N := by
  have ha := GeneralPaperPlanProfileMonotonicity.array_word W (n+2) (N+2) (by omega)
  have hP := Nat.add_le_add_left (Nat.mul_le_mul_left 72 ha) (128*W)
  exact Nat.add_le_add (Nat.mul_le_mul hN hP) (Nat.mul_le_mul_left 18 ha)

theorem bit_work {m k : ℕ} {cache : Cache m k} (W : ℕ) (learner : Learner) (state : State cache) (j : Fin m) :
    (run true (fun w => w) W learner state j).2≤GeneralPaperCellInstructionPrice.profile W (GeneralPaperBatchCounterPrice.limit k) :=
  (GeneralPaperCellInstructionPrice.bit_work W _ _).trans (profile_mono W _ _ (cell_count learner cache j))

theorem arithmetic_work {m k : ℕ} {cache : Cache m k} (learner : Learner) (state : State cache) (j : Fin m) :
    (run false (fun _ => 1) 1 learner state j).2≤GeneralPaperCellInstructionPrice.arithmeticProfile (GeneralPaperBatchCounterPrice.limit k) :=
  (GeneralPaperCellInstructionPrice.arithmetic_work _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_right 200 (cell_count learner cache j)) 18)

end Blotto.GeneralPaperActualEpochInstructions
