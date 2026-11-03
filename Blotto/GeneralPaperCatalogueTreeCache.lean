import Blotto.GeneralPaperCatalogueHorizon

/-! Generate the concrete epoch cache from four arrays of incoming sparse
tree nodes. All summary occurrences, their code bounds, ordering and initial
CDF certificates follow from the actual quantile descent. The shared power
table and comparison width are supplied prepared values, not rebuilt inside
the four summary traversals. The outer own-tree recurrence remains a join.
-/
namespace Blotto.GeneralPaperCatalogueTreeCache
open GeneralPaperCodeAlphabet GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure Trees (m depth : ℕ) where
  p : FixedArrayTable m (Node depth)
  q : FixedArrayTable m (Node depth)
  lambda : FixedArrayTable m (Node (depth+1))
  mu : FixedArrayTable m (Node (depth+1))

def initial (m depth : ℕ) : Trees m depth :=
  ⟨FixedArrayTable.ofFn (fun _ => .uniform depth 0),FixedArrayTable.ofFn (fun _ => .uniform depth 0),
    FixedArrayTable.ofFn (fun _ => .uniform (depth+1) 0),FixedArrayTable.ofFn (fun _ => .uniform (depth+1) 0)⟩

def treeHeight (learner : Learner) (lambda : ℕ) : ℕ :=
  match learner with
  | .p | .q => lambda
  | .lambda | .mu => lambda+1

def node {m lambda : ℕ} (learner : Learner) (trees : Trees m lambda) (j : Fin m) : Node (treeHeight learner lambda) :=
  match learner with
  | .p => trees.p.read j
  | .q => trees.q.read j
  | .lambda => trees.lambda.read j
  | .mu => trees.mu.read j

def summaries {m height : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (wordWidth k : ℕ) (nodes : FixedArrayTable m (Node height)) :
    FixedArrayTable m (Summary k) :=
  FixedArrayTable.ofFn (fun j => GeneralPaperInitialSummary.build powers wordWidth
    (GeneralPaperSourceParameters.prepare k).summarySize height (nodes.read j))

def prepare {m : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (wordWidth : ℕ) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) : Cache m k :=
  let p := summaries powers wordWidth k trees.p
  let q := summaries powers wordWidth k trees.q
  let lambda := summaries powers wordWidth k trees.lambda
  let mu := summaries powers wordWidth k trees.mu
  GeneralPaperCatalogueEpochCache.prepare a k p q lambda mu

def Valid {m : ℕ} (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) : Prop :=
  ∀ learner j, GeneralPaperIntervalCache.Valid a.lambda k (node learner trees j)

def Paths {m : ℕ} (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) : Prop :=
  ∀ learner j, PathBound (GeneralPaperPowerPrecision.levelBound a.lambda k) 0 (node learner trees j)

theorem initial_valid (m : ℕ) (a : Alphabet) (k : ℕ) : Valid a k (initial m a.lambda) := by
  intro learner j
  cases learner <;> simp only [node,initial,FixedArrayTable.read_ofFn] <;> exact Nat.zero_le _

theorem initial_paths (m : ℕ) (a : Alphabet) (k : ℕ) : Paths a k (initial m a.lambda) := by
  intro learner j i hi
  cases learner <;> simp only [node,initial,FixedArrayTable.read_ofFn,GeneralPaperIntervalLevels.levelAt,Nat.zero_add] <;> exact Nat.zero_le _

theorem tree_height_bound (learner : Learner) (lambda : ℕ) : treeHeight learner lambda≤lambda+1 := by
  cases learner <;> dsimp only [treeHeight] <;> omega

theorem summary_eq {m : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (wordWidth : ℕ) (a : Alphabet) (k : ℕ)
    (trees : Trees m a.lambda) (learner : Learner) (j : Fin m) :
    summary learner (prepare powers wordWidth a k trees) j=
      GeneralPaperInitialSummary.build powers wordWidth (GeneralPaperSourceParameters.prepare k).summarySize
        (treeHeight learner a.lambda) (node learner trees j) := by
  cases learner <;> simp only [summary,prepare,GeneralPaperCatalogueEpochCache.prepare,summaries,node,treeHeight,FixedArrayTable.read_ofFn]

theorem width_node {m : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (wordWidth : ℕ) (a : Alphabet) (k : ℕ)
    (trees : Trees m a.lambda) (learner : Learner) :
    GeneralPaperCatalogueEpochMetadata.width learner (prepare powers wordWidth a k trees)=2^(treeHeight learner a.lambda) :=
  GeneralPaperCatalogueEpochMetadata.width_power learner _

theorem codes_valid {m : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (wordWidth : ℕ) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    GeneralPaperCatalogueEpochMetadata.CodesValid (prepare powers wordWidth a k trees) := by
  intro learner j r
  rw [summary_eq,width_node]
  exact GeneralPaperInitialSummary.code_bounds _ _ _ _ _ r

theorem ordered {m : ℕ} (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    GeneralPaperCatalogueEpochMetadata.Ordered
      (prepare (GeneralPaperPreparedPowers.prepare a.lambda k) (GeneralPaperQuantileComparison.width a.lambda k) a k trees) := by
  intro learner j
  rw [summary_eq]
  exact GeneralPaperSummaryOrdered.summary_ordered a.lambda k _ _ (tree_height_bound learner a.lambda) (hValid learner j) (hPaths learner j)

theorem initial_close {m : ℕ} (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (learner : Learner) (j : Fin m) :
    GeneralPaperCDFReweighting.CDFClose (GeneralPaperTreeLaw.law k (node learner trees j))
      (GeneralPaperSummaryOccurrences.uniform
        (summary learner (prepare (GeneralPaperPreparedPowers.prepare a.lambda k) (GeneralPaperQuantileComparison.width a.lambda k) a k trees) j).read)
      (GeneralPaperCatalogueEpochMetadata.width learner
        (prepare (GeneralPaperPreparedPowers.prepare a.lambda k) (GeneralPaperQuantileComparison.width a.lambda k) a k trees)-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  rw [summary_eq,width_node]
  exact GeneralPaperTreeLaw.initial_close a.lambda k _ _ (tree_height_bound learner a.lambda) (hValid learner j) (hPaths learner j)

end Blotto.GeneralPaperCatalogueTreeCache
