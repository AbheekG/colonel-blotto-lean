import Blotto.GeneralPaperCatalogueOuterLoop

/-! The actual own-tree recurrence preserves the full-code level bound,
valid mass caches and path caps from its constructed uniform initializer.
All partial batches are covered by the existing sparse-update validity
theorem. Epoch-start quantile hypotheses are therefore derived invariants.
-/
namespace Blotto.GeneralPaperCatalogueOuterValidity
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Bounded {m : ℕ} (a : Alphabet) (trees : Trees m a.lambda) (bound : ℕ) : Prop :=
  ∀ learner j i, i<2^(treeHeight learner a.lambda) → levelAt (node learner trees j) i≤bound

theorem initial_bounded (m : ℕ) (a : Alphabet) : Bounded a (initial m a.lambda) 0 := by
  intro learner j i hi
  cases learner <;> simp only [node,initial,FixedArrayTable.read_ofFn,levelAt,le_refl]

theorem epoch_effect_bound {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) (learner : Learner) (j : Fin m) (i : ℕ) (hi : i<2^(treeHeight learner a.lambda)) :
    GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner
      (GeneralPaperCatalogueEpochRun.stateAt (epochRun (prepare a k Qv weights Bc Br) a k trees)
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j) i≤
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator) := by
  rw [epochRun_selected]
  let c := cache (prepare a k Qv weights Bc Br) a k trees
  have hw : GeneralPaperCatalogueEpochMetadata.width learner c=2^(treeHeight learner a.lambda) :=
    GeneralPaperCatalogueTreeCache.width_node _ _ a k trees learner
  exact GeneralPaperCatalogueCellHistory.batch_bound learner c Qv weights Bc Br _ le_rfl j ⟨i,by rw [hw]; exact hi⟩

theorem epoch_bounded {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) (bound : ℕ) (hBound : Bounded a trees bound) :
    Bounded a (epoch (prepare a k Qv weights Bc Br) a k trees).1
      (bound+(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) := by
  intro learner j i hi
  rw [epoch_trees,GeneralPaperCatalogueForestUpdate.updated_level a k Qv weights Bc Br trees _ learner j i hi]
  exact Nat.add_le_add (hBound learner j i hi) (epoch_effect_bound a k Qv weights Bc Br trees learner j i hi)

theorem trees_bounded {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    Bounded a (treesAt (prepare a k Qv weights Bc Br) a k count)
      (count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) := by
  induction count with
  | zero => simpa only [trees_initial,Nat.zero_mul] using initial_bounded m a
  | succ count ih =>
    rw [trees_step]
    have he := epoch_bounded a k Qv weights Bc Br _ _ ih
    convert he using 1 <;> ring

theorem boundary_cap {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    Bounded a (treesAt (prepare a k Qv weights Bc Br) a k count) (GeneralPaperPowerPrecision.levelBound a.lambda k) := by
  have hb := trees_bounded a k Qv weights Bc Br count
  have hc := Nat.mul_le_mul_right ((GeneralPaperTrajectoryParameters.prepare a.lambda k).period*
    (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) hCount
  intro learner j i hi
  have he := hb learner j i hi
  unfold GeneralPaperPowerPrecision.levelBound
  rw [GeneralPaperTrajectoryParameters.rows_product]
  nlinarith only [he,hc]

theorem trees_valid {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    Valid a k (treesAt (prepare a k Qv weights Bc Br) a k count) := by
  induction count with
  | zero => exact initial_valid m a k
  | succ count ih =>
    rw [trees_step,epoch_trees]
    apply GeneralPaperCatalogueForestUpdate.updated_valid a k Qv weights Bc Br _ _ (ih (by omega))
    intro learner j i hi
    have hc := boundary_cap a k Qv weights Bc Br (count+1) hCount learner j i hi
    rw [trees_step,epoch_trees,GeneralPaperCatalogueForestUpdate.updated_level a k Qv weights Bc Br _ _ learner j i hi] at hc
    exact hc

theorem trees_paths {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    Paths a k (treesAt (prepare a k Qv weights Bc Br) a k count) := by
  intro learner j i hi
  rw [Nat.zero_add]
  exact boundary_cap a k Qv weights Bc Br count hCount learner j i hi

theorem cache_ordered {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    GeneralPaperCatalogueEpochMetadata.Ordered (cacheAt (prepare a k Qv weights Bc Br) a k count) :=
  GeneralPaperCatalogueTreeCache.ordered a k _ (trees_valid a k Qv weights Bc Br count hCount)
    (trees_paths a k Qv weights Bc Br count hCount)

theorem cache_codes {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    GeneralPaperCatalogueEpochMetadata.CodesValid (cacheAt (prepare a k Qv weights Bc Br) a k count) :=
  GeneralPaperCatalogueTreeCache.codes_valid _ _ a k _

end Blotto.GeneralPaperCatalogueOuterValidity
