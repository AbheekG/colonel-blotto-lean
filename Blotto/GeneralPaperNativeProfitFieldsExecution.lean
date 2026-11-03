import Blotto.GeneralPaperNativeProfitLeafPrice

/-! One backward indexed reference-list loop assembles weighted native DP
fields. It calls the priced leaf builder once per real battlefield and
borrows the same stored weight in the returned pair. There is no index array,
weight-sum traversal or resource-tag reconstruction pass.
-/
namespace Blotto.GeneralPaperNativeProfitFieldsExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
variable {R : Type}

def element {m K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K))
    (j : Fin m) : GeneralPaperOrderedProfitTreeBuild.WeightedField R K × ℕ :=
  let field := GeneralPaperNativeProfitLeafExecution.run bits index price W T (weights.read j) (prefixes.read j) (plans.read j)
  ((field.1,weights.read j),field.2+64*W)

def run {m K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K) × ℕ :=
  GeneralPaperIndexedListPrice.run index (if bits then arrayWord W (m+2) else W) (element bits index price W T weights prefixes plans)

theorem data {m K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K))
    (hMesh : ∀ j,(plans.read j).mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index price W T weights prefixes plans).1=GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes plans := by
  rw [run,GeneralPaperIndexedListPrice.data]
  unfold GeneralPaperOrderedNativeProfitOptimizer.weightedFields
  congr 1
  funext j
  unfold element
  dsimp only
  rw [GeneralPaperNativeProfitLeafExecution.data bits index price W T _ _ _ (hMesh j)]

theorem length {m K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    (run bits index price W T weights prefixes plans).1.length=m := by
  rw [run,GeneralPaperIndexedListPrice.data,List.length_ofFn]

end Blotto.GeneralPaperNativeProfitFieldsExecution
