import Blotto.GeneralPaperOrderedTablePrice

/-! Full real-RAM table prices, with arithmetic bounded grid searches.
These do not assume a resource height or valid comparison budget. -/
namespace Blotto.GeneralPaperOrderedTableArithmetic
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

def leafProfile (K J depth : ℕ) : ℕ :=
  (64*J+44*(J+1)+64)+(136*K+18)+(K*((512*(depth+1)^2+336)+386)+64)+128

def mergeProfile (J depth : ℕ) : ℕ :=
  (64*J+44*(J+1)+64)+(136*J+18)+(J*(J*((512*(depth+1)^2+658)+386)+128)+64)+128

theorem leaf_work {K q w B : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) :
    (GeneralPaperOrderedTableExecution.leaf false (fun _ => 1) (fun _ => 1) 1 grid field).2≤leafProfile K grid.size grid.depth := by
  let initial := GeneralPaperDPTableControls.empty (Fin K) (fun _ => 1) 1 1 grid.size
  let labels := GeneralPaperDPTableControls.labels (fun _ => 1) 1 1 K
  have hf := GeneralPaperOrderedScatterArithmetic.fold_work (512*(grid.depth+1)^2+336)
    (GeneralPaperOrderedLeafEntryPrice.run false (fun _ => 1) 1 grid field) labels.1 initial.1
    (fun a _ => GeneralPaperOrderedLeafEntryPrice.arithmetic_work grid field a)
  have he := GeneralPaperDPTableControls.empty_arithmetic_work (Fin K) grid.size
  have hl := GeneralPaperDPTableControls.labels_arithmetic_work K
  have hLen : labels.1.length=K := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hf
  change initial.2+labels.2+(GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1
    (GeneralPaperOrderedLeafEntryPrice.run false (fun _ => 1) 1 grid field) labels.1 initial.1).2+128≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hl) hf) _

theorem merge_work {Left Right : Type*} {q w B : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (left : Table Tag Left grid.size) (right : Table Tag Right grid.size) :
    (GeneralPaperOrderedTableExecution.merge false (fun _ => 1) (fun _ => 1) 1 grid left right).2≤mergeProfile grid.size grid.depth := by
  let J := grid.size
  let initial := GeneralPaperDPTableControls.empty (Fin J × Fin J) (fun _ => 1) 1 1 J
  let labels := GeneralPaperDPTableControls.labels (fun _ => 1) 1 1 J
  have hf := GeneralPaperOrderedScatterArithmetic.rows_work (512*(grid.depth+1)^2+658)
    (GeneralPaperOrderedMergeEntryPrice.run false (fun _ => 1) 1 grid left right) labels.1 labels.1 initial.1
    (fun i _ j _ => GeneralPaperOrderedMergeEntryPrice.arithmetic_work grid left right i j)
  have he := GeneralPaperDPTableControls.empty_arithmetic_work (Fin J × Fin J) J
  have hl := GeneralPaperDPTableControls.labels_arithmetic_work J
  have hLen : labels.1.length=J := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hf
  change initial.2+labels.2+(GeneralPaperOrderedScatterExecution.rows (fun _ => 1) 1 1
    (GeneralPaperOrderedMergeEntryPrice.run false (fun _ => 1) 1 grid left right) labels.1 labels.1 initial.1).2+128≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hl) hf) _

end Blotto.GeneralPaperOrderedTableArithmetic
