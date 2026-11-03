import Blotto.GeneralPaperCatalogueShared

/-! Apply the four instruction families built from the already-returned
final epoch state. Each input tree is updated once by its own cell batch;
there is no replay of local rounds or replacement by uniform trees.
-/
namespace Blotto.GeneralPaperCatalogueForestUpdate
open GeneralPaperCodeAlphabet GeneralPaperCatalogueEpochCache GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueShared
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000

def updatedNode {m k : ℕ} {c : Cache m k} {a : Alphabet} (shared : Shared m) (learner : Learner)
    (trees : Trees m a.lambda) (state : State c) (j : Fin m) : Node (treeHeight learner a.lambda) :=
  (GeneralPaperIntervalBatch.run shared.powers (treeHeight learner a.lambda) (span learner shared)
    (node learner trees j) (GeneralPaperCatalogueCellHistory.batchOfState learner state j)).node

def apply {m k : ℕ} {c : Cache m k} {a : Alphabet} (shared : Shared m) (trees : Trees m a.lambda) (state : State c) : Trees m a.lambda :=
  ⟨FixedArrayTable.ofFn (updatedNode shared .p trees state),FixedArrayTable.ofFn (updatedNode shared .q trees state),
    FixedArrayTable.ofFn (updatedNode shared .lambda trees state),FixedArrayTable.ofFn (updatedNode shared .mu trees state)⟩

theorem node_apply {m k : ℕ} {c : Cache m k} {a : Alphabet} (shared : Shared m) (learner : Learner)
    (trees : Trees m a.lambda) (state : State c) (j : Fin m) :
    node learner (apply shared trees state) j=updatedNode shared learner trees state j := by
  cases learner <;> dsimp only [node,apply] <;> exact FixedArrayTable.read_ofFn _ j

theorem updated_level {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) (state : State (cache (prepare a k Qv weights Bc Br) a k trees))
    (learner : Learner) (j : Fin m) (i : ℕ) (hi : i<2^(treeHeight learner a.lambda)) :
    levelAt (node learner (apply (prepare a k Qv weights Bc Br) trees state) j) i=
      levelAt (node learner trees j) i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i := by
  rw [node_apply]
  exact GeneralPaperIntervalBatch.run_levels _ _ _ _ _ (span_power learner a k Qv weights Bc Br) i hi

theorem updated_valid {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) (state : State (cache (prepare a k Qv weights Bc Br) a k trees))
    (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees)
    (hFinal : ∀ learner j i, i<2^(treeHeight learner a.lambda) →
      levelAt (node learner trees j) i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound a.lambda k) :
    GeneralPaperCatalogueTreeCache.Valid a k (apply (prepare a k Qv weights Bc Br) trees state) := by
  intro learner j
  rw [node_apply]
  exact GeneralPaperIntervalBatch.run_valid a.lambda k _ _ _ _ (span_power learner a k Qv weights Bc Br)
    (hValid learner j) (hFinal learner j)

theorem updated_paths {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) (state : State (cache (prepare a k Qv weights Bc Br) a k trees))
    (hFinal : ∀ learner j i, i<2^(treeHeight learner a.lambda) →
      levelAt (node learner trees j) i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound a.lambda k) :
    Paths a k (apply (prepare a k Qv weights Bc Br) trees state) := by
  intro learner j i hi
  rw [Nat.zero_add,updated_level a k Qv weights Bc Br trees state learner j i hi]
  exact hFinal learner j i hi

end Blotto.GeneralPaperCatalogueForestUpdate
