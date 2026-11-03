import Blotto.GeneralPaperOrderedScatterExecution

/-! Every streaming comparison is priced from the current table invariant.
Callbacks execute once, with no generated-pair list, state validation pass or
replay of the minimum comparisons. Child tables remain borrowed references. -/
namespace Blotto.GeneralPaperOrderedScatterPrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
open GeneralPaperOrderedTableHeight
open GeneralPaperOrderedScatterExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

def entryProfile (price : ℕ → ℕ) (W A s : ℕ) : ℕ := 2*price (1+2*s)+192*W+128*A

theorem insert_work {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W A s : ℕ)
    (table : Table Tag Witness J) (entry : Entry Tag Witness J) (ht : Safe s table) (he : EntrySafe s entry) :
    (GeneralPaperOrderedScatterExecution.insert price W A table entry).2≤2*price (1+2*s)+128*W+128*A := by
  have h := GeneralPaperOrderedMinimumPrice.work price hMono W s (table.read entry.label) (some entry.selection)
    (ht entry.label) (by intro chosen hc; cases Option.some.inj hc; exact he)
  change (GeneralPaperOrderedMinimumPrice.run price W (table.read entry.label) (some entry.selection)).2+128*A≤_
  omega

theorem apply_work {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W A s : ℕ)
    (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J)) (ht : Safe s table) (he : OptionalSafe s entry) :
    (GeneralPaperOrderedScatterExecution.applyEntry price W A table entry).2≤entryProfile price W A s := by
  cases entry with
  | none => change 64*W≤_; unfold entryProfile; omega
  | some e =>
    have h := insert_work price hMono W A s table e ht (he e rfl)
    change (GeneralPaperOrderedScatterExecution.insert price W A table e).2+64*W≤_
    unfold entryProfile
    omega

theorem apply_safe {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A s : ℕ)
    (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J)) (ht : Safe s table) (he : OptionalSafe s entry) :
    Safe s (GeneralPaperOrderedScatterExecution.applyEntry price W A table entry).1 := by
  rw [apply_data]
  exact GeneralPaperOrderedTableHeight.apply_safe s table entry ht he

theorem fold_work {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W A s C : ℕ)
    (evaluate : α → Option (Entry Tag Witness J) × ℕ) (xs : List α) (table : Table Tag Witness J)
    (ht : Safe s table) (he : ∀ a∈xs,OptionalSafe s (evaluate a).1) (hc : ∀ a∈xs,(evaluate a).2≤C) :
    (GeneralPaperOrderedScatterExecution.fold price W A evaluate xs table).2≤xs.length*(C+entryProfile price W A s+64*W)+64*W := by
  induction xs generalizing table with
  | nil => change 64*W≤0*(C+entryProfile price W A s+64*W)+64*W; omega
  | cons a rest ih =>
    have ha := hc a List.mem_cons_self
    have hu := apply_work price hMono W A s table (evaluate a).1 ht (he a List.mem_cons_self)
    have hs := apply_safe price W A s table (evaluate a).1 ht (he a List.mem_cons_self)
    have hr := ih (GeneralPaperOrderedScatterExecution.applyEntry price W A table (evaluate a).1).1 hs
      (fun b hb => he b (List.mem_cons_of_mem _ hb)) (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    change (evaluate a).2+(GeneralPaperOrderedScatterExecution.applyEntry price W A table (evaluate a).1).2+
      (GeneralPaperOrderedScatterExecution.fold price W A evaluate rest
        (GeneralPaperOrderedScatterExecution.applyEntry price W A table (evaluate a).1).1).2+64*W≤_
    rw [List.length_cons]
    nlinarith only [ha,hu,hr]

theorem rows_work {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W A s C : ℕ)
    (evaluate : α → β → Option (Entry Tag Witness J) × ℕ) (columns : List β) (xs : List α) (table : Table Tag Witness J)
    (ht : Safe s table) (he : ∀ a∈xs,∀ b∈columns,OptionalSafe s (evaluate a b).1)
    (hc : ∀ a∈xs,∀ b∈columns,(evaluate a b).2≤C) :
    (GeneralPaperOrderedScatterExecution.rows price W A evaluate columns xs table).2≤
      xs.length*(columns.length*(C+entryProfile price W A s+64*W)+128*W)+64*W := by
  induction xs generalizing table with
  | nil => change 64*W≤0*(columns.length*(C+entryProfile price W A s+64*W)+128*W)+64*W; omega
  | cons a rest ih =>
    have hf := fold_work price hMono W A s C (evaluate a) columns table ht (he a List.mem_cons_self) (hc a List.mem_cons_self)
    have hs : Safe s (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).1 := by
      rw [fold_data]
      exact GeneralPaperOrderedTableHeight.fold_safe s _ columns table ht (he a List.mem_cons_self)
    have hr := ih (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).1 hs
      (fun b hb => he b (List.mem_cons_of_mem _ hb)) (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    change (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).2+
      (GeneralPaperOrderedScatterExecution.rows price W A evaluate columns rest
        (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).1).2+64*W≤_
    rw [List.length_cons]
    nlinarith only [hf,hr]

end Blotto.GeneralPaperOrderedScatterPrice
