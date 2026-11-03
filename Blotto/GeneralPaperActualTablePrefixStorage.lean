import Blotto.GeneralPaperDPControlStorage

/-! Native leaf/merge constructors derive candidate resource heights and
typed predecessor caps for every streamed table prefix and loop workspace.
The merge owns one J-label list; no J-by-J candidate array is allocated. -/
namespace Blotto.GeneralPaperActualTablePrefixStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def pairBits {J : ℕ} (ij : Fin J × Fin J) : ℕ := rankBits ij.1+rankBits ij.2

theorem pair_bound {J : ℕ} (ij : Fin J × Fin J) : pairBits ij≤2*rankWord J := by
  have hi := rank_bound ij.1
  have hj := rank_bound ij.2
  unfold pairBits
  omega

theorem leaf_prefix {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A s count : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K)
    (hl : ∀ i,RationalHeight (field.read i).2.threshold s) :
    tableFootprint W rankBits (GeneralPaperOrderedScatterExecution.fold price W A
      (GeneralPaperOrderedLeafEntryPrice.run bits price W grid field)
      ((GeneralPaperDPTableControls.labels index W A K).1.take count)
      (GeneralPaperDPTableControls.empty (Fin K) index W A grid.size).1).1≤
        tableProfile W grid.size (rankWord K) s := by
  apply GeneralPaperStreamingScatterStorage.fold_prefix price W A (rankWord K) s count rankBits rank_bound
  · rw [GeneralPaperDPTableControls.empty_data]
    exact empty_safe _ _ s
  · intro i _
    exact GeneralPaperOrderedLeafEntryPrice.safe bits price W s grid field i (hl i)

theorem leaf_peak {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K)
    (hl : ∀ i,RationalHeight (field.read i).2.threshold s) :
    GeneralPaperStreamingScatterStorage.foldPeak price W A (GeneralPaperDPControlStorage.frame W K grid.size) rankBits
      (GeneralPaperOrderedLeafEntryPrice.run bits price W grid field)
      (GeneralPaperDPTableControls.labels index W A K).1
      (GeneralPaperDPTableControls.empty (Fin K) index W A grid.size).1≤
        applyProfile W grid.size (rankWord K) s+GeneralPaperDPControlStorage.frame W K grid.size := by
  apply GeneralPaperStreamingScatterStorage.fold_bound price W A _ (rankWord K) s rankBits rank_bound
  · rw [GeneralPaperDPTableControls.empty_data]
    exact empty_safe _ _ s
  · intro i _
    exact GeneralPaperOrderedLeafEntryPrice.safe bits price W s grid field i (hl i)

theorem merge_prefix {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A s h rowCount colCount : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (hl : Safe (expressionHeightBudget s h) left) (hr : Safe (expressionHeightBudget s h) right) (i : Fin grid.size) :
    let labels := (GeneralPaperDPTableControls.labels index W A grid.size).1
    let evaluate := GeneralPaperOrderedMergeEntryPrice.run bits price W grid left right
    let previous := (GeneralPaperOrderedScatterExecution.rows price W A evaluate labels (labels.take rowCount)
      (GeneralPaperDPTableControls.empty (Fin grid.size × Fin grid.size) index W A grid.size).1).1
    tableFootprint W pairBits (GeneralPaperOrderedScatterExecution.fold price W A (evaluate i) (labels.take colCount) previous).1≤
      tableProfile W grid.size (2*rankWord grid.size) (expressionHeightBudget s (h+1)) := by
  dsimp only
  apply GeneralPaperStreamingScatterStorage.rows_prefix price W A (2*rankWord grid.size)
    (expressionHeightBudget s (h+1)) rowCount colCount pairBits pair_bound
  · rw [GeneralPaperDPTableControls.empty_data]
    exact empty_safe _ _ _
  · intro i _ j _
    exact GeneralPaperOrderedMergeEntryPrice.safe bits price W s h grid left right i j hl hr
  · rw [GeneralPaperDPTableControls.labels_data]
    exact List.mem_finRange i

theorem merge_peak {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A s h : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (hl : Safe (expressionHeightBudget s h) left) (hr : Safe (expressionHeightBudget s h) right) :
    let labels := (GeneralPaperDPTableControls.labels index W A grid.size).1
    GeneralPaperStreamingScatterStorage.rowsPeak price W A (GeneralPaperDPControlStorage.frame W grid.size grid.size) pairBits
      (GeneralPaperOrderedMergeEntryPrice.run bits price W grid left right) labels labels
      (GeneralPaperDPTableControls.empty (Fin grid.size × Fin grid.size) index W A grid.size).1≤
        applyProfile W grid.size (2*rankWord grid.size) (expressionHeightBudget s (h+1))+
          2*GeneralPaperDPControlStorage.frame W grid.size grid.size := by
  dsimp only
  apply GeneralPaperStreamingScatterStorage.rows_bound price W A _ (2*rankWord grid.size)
    (expressionHeightBudget s (h+1)) pairBits pair_bound
  · rw [GeneralPaperDPTableControls.empty_data]
    exact empty_safe _ _ _
  · intro i _ j _
    exact GeneralPaperOrderedMergeEntryPrice.safe bits price W s h grid left right i j hl hr

end Blotto.GeneralPaperActualTablePrefixStorage
