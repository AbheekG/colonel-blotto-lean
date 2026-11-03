import Blotto.GeneralPaperCatalogueOuterValidity

/-! One global code-dependent history extracted from the actual own-tree
outer execution by quotient/remainder. End-of-epoch sparse levels equal its
full prefix sums. The signed magnitude remains one, preserving the paper's
four squared caps 4+4+1+1 rather than weakening them all to four.
-/
namespace Blotto.GeneralPaperCatalogueGlobalHistory
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000

def increment {m : ℕ} (learner : Learner) (shared : Shared m) (a : Alphabet) (k time : ℕ) (j : Fin m) (code : ℕ) : ℕ :=
  GeneralPaperCatalogueOccurrenceHistory.increment learner
    (epochRun shared a k (treesAt shared a k (time/shared.trajectory.period))) (time%shared.trajectory.period) j code

theorem period_positive (lambda k : ℕ) : 0<(GeneralPaperTrajectoryParameters.prepare lambda k).period := by
  rw [GeneralPaperTrajectoryParameters.period_power]
  exact Nat.two_pow_pos _

theorem increment_at {m : ℕ} (learner : Learner) (shared : Shared m) (a : Alphabet) (k epoch time : ℕ)
    (hp : 0<shared.trajectory.period) (ht : time<shared.trajectory.period) (j : Fin m) (code : ℕ) :
    increment learner shared a k (epoch*shared.trajectory.period+time) j code=
      GeneralPaperCatalogueOccurrenceHistory.increment learner (epochRun shared a k (treesAt shared a k epoch)) time j code := by
  have hd : (epoch*shared.trajectory.period+time)/shared.trajectory.period=epoch := by
    rw [Nat.add_comm (epoch*shared.trajectory.period),Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt ht,Nat.zero_add]
  have hm : (epoch*shared.trajectory.period+time)%shared.trajectory.period=time := by
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,Nat.mod_eq_of_lt ht]
  change GeneralPaperCatalogueOccurrenceHistory.increment learner
    (epochRun shared a k (treesAt shared a k ((epoch*shared.trajectory.period+time)/shared.trajectory.period)))
    ((epoch*shared.trajectory.period+time)%shared.trajectory.period) j code=_
  simpa only [hm] using congrArg (fun e => GeneralPaperCatalogueOccurrenceHistory.increment learner
    (epochRun shared a k (treesAt shared a k e)) ((epoch*shared.trajectory.period+time)%shared.trajectory.period) j code) hd

theorem increment_bound {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (code : ℕ) :
    increment learner (prepare a k Qv weights Bc Br) a k time j code≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  unfold increment
  rw [epochRun_selected]
  exact GeneralPaperCatalogueLossBounds.increment_bound learner _ Qv weights Bc Br _
    (Nat.mod_lt time (period_positive a.lambda k)).le j code

def magnitude (learner : Learner) : ℝ :=
  match learner with
  | .p | .q => 2
  | .lambda | .mu => 1

theorem sharp_magnitude {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (code : ℕ) :
    |(GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (increment learner (prepare a k Qv weights Bc Br) a k time j code):ℝ)|≤magnitude learner := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  let run := GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br
  let localTime := time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  have ht : localTime≤(GeneralPaperTrajectoryParameters.prepare c.alphabet.lambda k).period :=
    (Nat.mod_lt time (period_positive a.lambda k)).le
  have he := GeneralPaperAdaptiveLossBounds.magnitudes
    (GeneralPaperCatalogueEpochRun.fieldAt run localTime j) (GeneralPaperCatalogueEpochRun.snapshotAt run localTime j)
    (GeneralPaperCatalogueEpochRun.choiceAt run localTime j)
    (GeneralPaperCatalogueEpochRun.selected_positive c Qv weights Bc Br localTime ht j)
    (GeneralPaperCatalogueEpochRun.snapshot_coherent run localTime j)
  unfold increment
  rw [epochRun_selected]
  cases learner with
  | p => exact he.1 code
  | q => exact he.2.1 code
  | lambda => exact he.2.2.1 code
  | mu => exact he.2.2.2 code

theorem epoch_batch_sum {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (j : Fin m)
    (i : ℕ) (hi : i<2^(treeHeight learner a.lambda)) :
    GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner
      (GeneralPaperCatalogueEpochRun.stateAt (epochRun (prepare a k Qv weights Bc Br) a k
        (treesAt (prepare a k Qv weights Bc Br) a k epoch)) (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j) i=
      ∑ t ∈ Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).period,
        increment learner (prepare a k Qv weights Bc Br) a k (epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+t) j i := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k epoch
  have hw : GeneralPaperCatalogueEpochMetadata.width learner c=2^(treeHeight learner a.lambda) :=
    GeneralPaperCatalogueTreeCache.width_node _ _ a k _ learner
  let code : Fin (GeneralPaperCatalogueEpochMetadata.width learner c) := ⟨i,by rw [hw]; exact hi⟩
  have hb := GeneralPaperCatalogueCellHistory.batch_effect learner (GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br)
    (GeneralPaperCatalogueOuterValidity.cache_ordered a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) (GeneralPaperTrajectoryParameters.prepare a.lambda k).period j code
  rw [GeneralPaperGeometricLevels.levels_sum] at hb
  rw [epochRun_selected]
  refine hb.trans ?_
  apply Finset.sum_congr rfl
  intro t ht
  exact (increment_at learner _ a k epoch t (period_positive a.lambda k) (Finset.mem_range.mp ht) j i).symm

theorem tree_levels {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (j : Fin m)
    (i : ℕ) (hi : i<2^(treeHeight learner a.lambda)) :
    levelAt (node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j) i=
      ∑ t ∈ Finset.range (epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period),
        increment learner (prepare a k Qv weights Bc Br) a k t j i := by
  induction epoch with
  | zero =>
    cases learner <;> simp only [treesAt,execute,node,initial,FixedArrayTable.read_ofFn,levelAt,Nat.zero_mul,Finset.range_zero,Finset.sum_empty]
  | succ epoch ih =>
    rw [trees_step,epoch_trees,GeneralPaperCatalogueForestUpdate.updated_level a k Qv weights Bc Br _ _ learner j i hi,ih (by omega)]
    calc
      _ = (∑ t ∈ Finset.range (epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period),
          increment learner (prepare a k Qv weights Bc Br) a k t j i)+
          ∑ t ∈ Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).period,
            increment learner (prepare a k Qv weights Bc Br) a k (epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+t) j i :=
        congrArg (fun v => (∑ t ∈ Finset.range (epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period),
          increment learner (prepare a k Qv weights Bc Br) a k t j i)+v)
          (epoch_batch_sum learner a k Qv weights Bc Br epoch (by omega) j i hi)
      _ = _ := by rw [Nat.succ_mul,Finset.sum_range_add]

end Blotto.GeneralPaperCatalogueGlobalHistory
