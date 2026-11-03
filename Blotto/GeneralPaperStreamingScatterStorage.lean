import Blotto.GeneralPaperEncodedScatterStorage

/-! Workspace of the paper's linear mutable scatter schedule. Current
candidate/old/new slots are released before the next callback; phase-price
annotations are erased. Each nested loop retains its scalar/reference
control reserve, while callbacks' arithmetic scratch is a separate phase. -/
namespace Blotto.GeneralPaperStreamingScatterStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedTableHeight
open GeneralPaperEncodedScatterStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def foldPeak {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A C : ℕ) (encode : Witness → ℕ)
    (evaluate : α → Option (Entry Tag Witness J) × ℕ) : List α → Table Tag Witness J → ℕ
  | [],table => tableFootprint W encode table+C
  | a::rest,table => max (applyWindow price W A encode table (evaluate a).1+C)
      (foldPeak price W A C encode evaluate rest (GeneralPaperOrderedScatterExecution.applyEntry price W A table (evaluate a).1).1)

theorem fold_bound {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A C P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (evaluate : α → Option (Entry Tag Witness J) × ℕ)
    (xs : List α) (table : Table Tag Witness J) (ht : Safe s table)
    (hs : ∀ a∈xs,OptionalSafe s (evaluate a).1) :
    foldPeak price W A C encode evaluate xs table≤applyProfile W J P s+C := by
  induction xs generalizing table with
  | nil =>
    have hb := table_bound W P s encode he table ht
    simp only [foldPeak,applyProfile]
    omega
  | cons a rest ih =>
    have ha := apply_bound price W A P s encode he table (evaluate a).1 ht (hs a List.mem_cons_self)
    have ht' := GeneralPaperOrderedScatterPrice.apply_safe price W A s table (evaluate a).1 ht (hs a List.mem_cons_self)
    have hr := ih _ ht' (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    exact max_le (Nat.add_le_add_right ha C) hr

def rowsPeak {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A C : ℕ) (encode : Witness → ℕ)
    (evaluate : α → β → Option (Entry Tag Witness J) × ℕ) (columns : List β) : List α → Table Tag Witness J → ℕ
  | [],table => tableFootprint W encode table+2*C
  | a::rest,table => max (foldPeak price W A C encode (evaluate a) columns table+C)
      (rowsPeak price W A C encode evaluate columns rest (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).1)

theorem rows_bound {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A C P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (evaluate : α → β → Option (Entry Tag Witness J) × ℕ)
    (columns : List β) (xs : List α) (table : Table Tag Witness J) (ht : Safe s table)
    (hs : ∀ a∈xs,∀ b∈columns,OptionalSafe s (evaluate a b).1) :
    rowsPeak price W A C encode evaluate columns xs table≤applyProfile W J P s+2*C := by
  induction xs generalizing table with
  | nil =>
    have hb := table_bound W P s encode he table ht
    simp only [rowsPeak,applyProfile]
    omega
  | cons a rest ih =>
    have ha := fold_bound price W A C P s encode he (evaluate a) columns table ht (hs a List.mem_cons_self)
    have ht' : Safe s (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) columns table).1 := by
      rw [GeneralPaperOrderedScatterExecution.fold_data]
      exact fold_safe s _ columns table ht (hs a List.mem_cons_self)
    have hr := ih _ ht' (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    exact max_le (by omega) hr

theorem fold_prefix {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A P s count : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (evaluate : α → Option (Entry Tag Witness J) × ℕ)
    (xs : List α) (table : Table Tag Witness J) (ht : Safe s table)
    (hs : ∀ a∈xs,OptionalSafe s (evaluate a).1) :
    tableFootprint W encode (GeneralPaperOrderedScatterExecution.fold price W A evaluate (xs.take count) table).1≤tableProfile W J P s := by
  apply table_bound W P s encode he
  rw [GeneralPaperOrderedScatterExecution.fold_data]
  exact fold_safe s _ _ _ ht (fun a ha => hs a (List.mem_of_mem_take ha))

theorem rows_prefix {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A P s rowCount colCount : ℕ)
    (encode : Witness → ℕ) (he : ∀ witness,encode witness≤P)
    (evaluate : α → β → Option (Entry Tag Witness J) × ℕ) (columns : List β) (xs : List α)
    (table : Table Tag Witness J) (ht : Safe s table)
    (hs : ∀ a∈xs,∀ b∈columns,OptionalSafe s (evaluate a b).1) (a : α) (ha : a∈xs) :
    let previous := (GeneralPaperOrderedScatterExecution.rows price W A evaluate columns (xs.take rowCount) table).1
    tableFootprint W encode (GeneralPaperOrderedScatterExecution.fold price W A (evaluate a) (columns.take colCount) previous).1≤tableProfile W J P s := by
  dsimp only
  apply table_bound W P s encode he
  rw [GeneralPaperOrderedScatterExecution.fold_data,GeneralPaperOrderedScatterExecution.rows_data]
  exact fold_safe s _ _ _ (rows_safe s _ _ _ _ ht (fun a ha => hs a (List.mem_of_mem_take ha)))
    (fun b hb => hs a ha b (List.mem_of_mem_take hb))

end Blotto.GeneralPaperStreamingScatterStorage
