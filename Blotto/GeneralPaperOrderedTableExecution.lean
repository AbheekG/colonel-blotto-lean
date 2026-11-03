import Blotto.GeneralPaperOrderedMergeEntryPrice

/-! Actual leaf/merge table drivers, each with one empty output table.
Leaf option labels are constructed once; a merge shares one index list
between both loop dimensions. Candidates stream directly into the table. -/
namespace Blotto.GeneralPaperOrderedTableExecution
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000

def leaf {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) : Table Tag (Fin K) grid.size × ℕ :=
  let A := if bits then arrayWord W grid.size else W
  let initial := GeneralPaperDPTableControls.empty (Fin K) index W A grid.size
  let labels := GeneralPaperDPTableControls.labels index W (if bits then arrayWord W (K+2) else W) K
  let filled := GeneralPaperOrderedScatterExecution.fold price W A
    (GeneralPaperOrderedLeafEntryPrice.run bits price W grid field) labels.1 initial.1
  (filled.1,initial.2+labels.2+filled.2+128*W)

def merge {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size) :
    Table Tag (Fin grid.size × Fin grid.size) grid.size × ℕ :=
  let A := if bits then arrayWord W grid.size else W
  let initial := GeneralPaperDPTableControls.empty (Fin grid.size × Fin grid.size) index W A grid.size
  let labels := GeneralPaperDPTableControls.labels index W (if bits then arrayWord W (grid.size+2) else W) grid.size
  let filled := GeneralPaperOrderedScatterExecution.rows price W A
    (GeneralPaperOrderedMergeEntryPrice.run bits price W grid left right) labels.1 labels.1 initial.1
  (filled.1,initial.2+labels.2+filled.2+128*W)

theorem leaf_data {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) :
    (leaf bits index price W grid field).1=leafTable grid field := by
  unfold leaf
  dsimp only
  rw [GeneralPaperOrderedScatterExecution.fold_data,GeneralPaperDPTableControls.labels_data,GeneralPaperDPTableControls.empty_data]
  have he : (fun a => (GeneralPaperOrderedLeafEntryPrice.run bits price W grid field a).1)=
      (fun a => some (leafEntry grid field a)) := funext (fun a => GeneralPaperOrderedLeafEntryPrice.data bits price W grid field a)
  rw [he]
  rfl

theorem merge_data {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size) :
    (merge bits index price W grid left right).1=mergeTable grid left right := by
  unfold merge
  dsimp only
  rw [GeneralPaperOrderedScatterExecution.rows_data,GeneralPaperDPTableControls.labels_data,GeneralPaperDPTableControls.empty_data]
  have he : (fun i j => (GeneralPaperOrderedMergeEntryPrice.run bits price W grid left right i j).1)=mergeEntry grid left right :=
    funext (fun i => funext (fun j => GeneralPaperOrderedMergeEntryPrice.data bits price W grid left right i j))
  rw [he]
  rfl

end Blotto.GeneralPaperOrderedTableExecution
