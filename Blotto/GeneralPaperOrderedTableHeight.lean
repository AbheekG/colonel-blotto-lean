import Blotto.GeneralPaperOrderedMinimumPrice

/-! Heights are preserved through every intermediate scatter table, not
only the final DP state. The predicates are erased and perform no scans. -/
namespace Blotto.GeneralPaperOrderedTableHeight
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
set_option autoImplicit false
set_option maxHeartbeats 5000000

def Safe {Witness : Type*} {J : ℕ} (s : ℕ) (table : Table Tag Witness J) : Prop :=
  ∀ i,GeneralPaperOrderedMinimumPrice.Safe s (table.read i)

def EntrySafe {Witness : Type*} {J : ℕ} (s : ℕ) (entry : Entry Tag Witness J) : Prop :=
  RationalHeight entry.selection.cost.threshold s

def OptionalSafe {Witness : Type*} {J : ℕ} (s : ℕ) (entry : Option (Entry Tag Witness J)) : Prop :=
  ∀ e,entry=some e → EntrySafe s e

theorem empty_safe (Witness : Type*) (J s : ℕ) : Safe s (empty (R:=Tag) Witness J) := by
  intro i chosen h
  rw [empty,FixedArrayTable.read_ofFn] at h
  contradiction

theorem insert_safe {Witness : Type*} {J : ℕ} (s : ℕ) (table : Table Tag Witness J) (entry : Entry Tag Witness J)
    (ht : Safe s table) (he : EntrySafe s entry) : Safe s (insert table entry) := by
  intro i
  rw [GeneralPaperOrderedProfitScatter.insert,FixedArrayTable.read_write]
  split
  · exact GeneralPaperOrderedMinimumPrice.pick_safe s _ _ (ht entry.label)
      (by intro chosen hc; cases Option.some.inj hc; exact he)
  · exact ht i

theorem apply_safe {Witness : Type*} {J : ℕ} (s : ℕ) (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J))
    (ht : Safe s table) (he : OptionalSafe s entry) : Safe s (applyEntry table entry) := by
  cases entry with
  | none => exact ht
  | some e => exact insert_safe s table e ht (he e rfl)

theorem fold_safe {α Witness : Type*} {J : ℕ} (s : ℕ) (evaluate : α → Option (Entry Tag Witness J))
    (xs : List α) (table : Table Tag Witness J) (ht : Safe s table)
    (he : ∀ a∈xs,OptionalSafe s (evaluate a)) : Safe s (fold evaluate xs table) := by
  induction xs generalizing table with
  | nil => exact ht
  | cons a rest ih =>
    exact ih _ (apply_safe s table (evaluate a) ht (he a List.mem_cons_self))
      (fun b hb => he b (List.mem_cons_of_mem _ hb))

theorem rows_safe {α β Witness : Type*} {J : ℕ} (s : ℕ) (evaluate : α → β → Option (Entry Tag Witness J))
    (columns : List β) (xs : List α) (table : Table Tag Witness J) (ht : Safe s table)
    (he : ∀ a∈xs,∀ b∈columns,OptionalSafe s (evaluate a b)) : Safe s (rows evaluate columns xs table) := by
  induction xs generalizing table with
  | nil => exact ht
  | cons a rest ih =>
    exact ih _ (fold_safe s (evaluate a) columns table ht (he a List.mem_cons_self))
      (fun b hb => he b (List.mem_cons_of_mem _ hb))

end Blotto.GeneralPaperOrderedTableHeight
