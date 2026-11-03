import Blotto.GeneralPaperOrderedTableExecution

/-! Full bit prices of the actual streaming leaf and merge tables. Empty
tables/index lists are built once. Every comparison uses an intermediate
table height invariant; resource words remain dependent on subtree height. -/
namespace Blotto.GeneralPaperOrderedTablePrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000

def leafProfile (price : ℕ → ℕ) (W m lambda k Qv K J s : ℕ) : ℕ :=
  GeneralPaperDPTableControls.emptyProfile W J+GeneralPaperDPTableControls.labelsProfile W K+
    (K*(GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+128*W+
      GeneralPaperOrderedScatterPrice.entryProfile price W (arrayWord W J) s+64*W)+64*W)+128*W

def mergeProfile (price : ℕ → ℕ) (W m lambda k Qv J s h : ℕ) : ℕ :=
  GeneralPaperDPTableControls.emptyProfile W J+GeneralPaperDPTableControls.labelsProfile W J+
    (J*(J*(GeneralPaperOrderedMergeEntryPrice.profile price W m lambda k Qv J s h+
      GeneralPaperOrderedScatterPrice.entryProfile price W (arrayWord W J) (expressionHeightBudget s (h+1))+64*W)+128*W)+64*W)+128*W

theorem leaf_work {K : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv s : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (field : Field Tag K) (hs : ∀ a,RationalHeight (field.read a).2.threshold s)
    (hNum : ∀ a,(field.read a).1≤2*prepared.parameters.qProf) :
    (GeneralPaperOrderedTableExecution.leaf true (fun x => x) price W prepared.grid field).2≤
      leafProfile price W m lambda k Qv K prepared.grid.size s := by
  let A := arrayWord W prepared.grid.size
  let initial := GeneralPaperDPTableControls.empty (Fin K) (fun x => x) W A prepared.grid.size
  let labels := GeneralPaperDPTableControls.labels (fun x => x) W (arrayWord W (K+2)) K
  have hInitial : GeneralPaperOrderedTableHeight.Safe s initial.1 := by
    rw [GeneralPaperDPTableControls.empty_data]
    exact GeneralPaperOrderedTableHeight.empty_safe _ _ s
  have hf := GeneralPaperOrderedScatterPrice.fold_work price hMono W A s
    (GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+128*W)
    (GeneralPaperOrderedLeafEntryPrice.run true price W prepared.grid field) labels.1 initial.1 hInitial
    (fun a _ => GeneralPaperOrderedLeafEntryPrice.safe true price W s prepared.grid field a (hs a))
    (fun a _ => GeneralPaperOrderedLeafEntryPrice.bit_work price hMono W m lambda k Qv prepared hp field a (hNum a))
  have he := GeneralPaperDPTableControls.empty_bit_work (Fin K) W prepared.grid.size
  have hl := GeneralPaperDPTableControls.labels_bit_work W K
  have hLen : labels.1.length=K := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hf
  change initial.2+labels.2+(GeneralPaperOrderedScatterExecution.fold price W A
    (GeneralPaperOrderedLeafEntryPrice.run true price W prepared.grid field) labels.1 initial.1).2+128*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hl) hf) _

theorem merge_work {Left Right : Type*} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv s h : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (left : Table Tag Left prepared.grid.size) (right : Table Tag Right prepared.grid.size)
    (hl : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) left)
    (hr : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) right) :
    (GeneralPaperOrderedTableExecution.merge true (fun x => x) price W prepared.grid left right).2≤
      mergeProfile price W m lambda k Qv prepared.grid.size s h := by
  let J := prepared.grid.size
  let A := arrayWord W J
  let S := expressionHeightBudget s (h+1)
  let initial := GeneralPaperDPTableControls.empty (Fin J × Fin J) (fun x => x) W A J
  let labels := GeneralPaperDPTableControls.labels (fun x => x) W (arrayWord W (J+2)) J
  have hInitial : GeneralPaperOrderedTableHeight.Safe S initial.1 := by
    rw [GeneralPaperDPTableControls.empty_data]
    exact GeneralPaperOrderedTableHeight.empty_safe _ _ S
  have hf := GeneralPaperOrderedScatterPrice.rows_work price hMono W A S
    (GeneralPaperOrderedMergeEntryPrice.profile price W m lambda k Qv J s h)
    (GeneralPaperOrderedMergeEntryPrice.run true price W prepared.grid left right) labels.1 labels.1 initial.1 hInitial
    (fun i _ j _ => GeneralPaperOrderedMergeEntryPrice.safe true price W s h prepared.grid left right i j hl hr)
    (fun i _ j _ => GeneralPaperOrderedMergeEntryPrice.bit_work price hMono W m lambda k Qv s h prepared hp left right i j hl hr)
  have he := GeneralPaperDPTableControls.empty_bit_work (Fin J × Fin J) W J
  have hLabels := GeneralPaperDPTableControls.labels_bit_work W J
  have hLen : labels.1.length=J := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hf
  change initial.2+labels.2+(GeneralPaperOrderedScatterExecution.rows price W A
    (GeneralPaperOrderedMergeEntryPrice.run true price W prepared.grid left right) labels.1 labels.1 initial.1).2+128*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hLabels) hf) _

end Blotto.GeneralPaperOrderedTablePrice
