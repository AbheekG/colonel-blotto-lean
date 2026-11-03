import Blotto.GeneralPaperBalancedTagWords

/-! One data-producing streaming scatter. Each callback executes once and
updates one table entry. A prices local array indices/references; W prices
other references. The output table is threaded linearly between writes. -/
namespace Blotto.GeneralPaperOrderedScatterExecution
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
set_option autoImplicit false
set_option maxHeartbeats 5000000

def insert {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (table : Table Tag Witness J) (entry : Entry Tag Witness J) : Table Tag Witness J × ℕ :=
  let chosen := GeneralPaperOrderedMinimumPrice.run price W (table.read entry.label) (some entry.selection)
  (table.write entry.label chosen.1,chosen.2+128*A)

def applyEntry {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ) (table : Table Tag Witness J) :
    Option (Entry Tag Witness J) → Table Tag Witness J × ℕ
  | none => (table,64*W)
  | some entry => let updated := insert price W A table entry; (updated.1,updated.2+64*W)

def fold {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (evaluate : α → Option (Entry Tag Witness J) × ℕ) : List α → Table Tag Witness J → Table Tag Witness J × ℕ
  | [],table => (table,64*W)
  | a::rest,table =>
    let current := evaluate a
    let updated := applyEntry price W A table current.1
    let later := fold price W A evaluate rest updated.1
    (later.1,current.2+updated.2+later.2+64*W)

def rows {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (evaluate : α → β → Option (Entry Tag Witness J) × ℕ) (columns : List β) :
    List α → Table Tag Witness J → Table Tag Witness J × ℕ
  | [],table => (table,64*W)
  | a::rest,table =>
    let current := fold price W A (evaluate a) columns table
    let later := rows price W A evaluate columns rest current.1
    (later.1,current.2+later.2+64*W)

theorem insert_data {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (table : Table Tag Witness J) (entry : Entry Tag Witness J) :
    (insert price W A table entry).1=GeneralPaperOrderedProfitScatter.insert table entry := by
  simp only [insert,GeneralPaperOrderedMinimumPrice.data,GeneralPaperOrderedProfitScatter.insert]

theorem apply_data {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J)) :
    (applyEntry price W A table entry).1=GeneralPaperOrderedProfitScatter.applyEntry table entry := by
  cases entry with
  | none => rfl
  | some entry => exact insert_data price W A table entry

theorem fold_data {α Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (evaluate : α → Option (Entry Tag Witness J) × ℕ) (xs : List α) (table : Table Tag Witness J) :
    (fold price W A evaluate xs table).1=GeneralPaperOrderedProfitScatter.fold (fun a => (evaluate a).1) xs table := by
  induction xs generalizing table with
  | nil => rfl
  | cons a rest ih =>
    rw [fold]
    dsimp only
    rw [ih,apply_data]
    rfl

theorem rows_data {α β Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ)
    (evaluate : α → β → Option (Entry Tag Witness J) × ℕ) (columns : List β) (xs : List α) (table : Table Tag Witness J) :
    (rows price W A evaluate columns xs table).1=GeneralPaperOrderedProfitScatter.rows (fun a b => (evaluate a b).1) columns xs table := by
  induction xs generalizing table with
  | nil => rfl
  | cons a rest ih =>
    rw [rows]
    dsimp only
    rw [ih,fold_data]
    rfl

end Blotto.GeneralPaperOrderedScatterExecution
