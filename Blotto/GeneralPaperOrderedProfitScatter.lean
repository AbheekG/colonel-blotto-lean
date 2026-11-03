import Blotto.GeneralPaperOrderedMinimum

/-! Stream candidates into a native minimum-resource table. Each candidate
updates only its rounded label. The reference predicates below are erased;
the runtime stores no list of generated pairs or full allocation products.
-/
namespace Blotto.GeneralPaperOrderedProfitScatter
open GeneralPaperOrderedMinimum
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

structure Entry (R : Type) (Witness : Type*) (J : ℕ) where
  label : Fin J
  selection : Selection R Witness

abbrev Table (R : Type) (Witness : Type*) (J : ℕ) := FixedArrayTable J (Option (Selection R Witness))

def empty (Witness : Type*) (J : ℕ) : Table R Witness J := FixedArrayTable.ofFn (fun _ => none)

def insert {Witness : Type*} {J : ℕ} (table : Table R Witness J) (entry : Entry R Witness J) : Table R Witness J :=
  table.write entry.label (pick (table.read entry.label) (some entry.selection))

def applyEntry {Witness : Type*} {J : ℕ} (table : Table R Witness J) : Option (Entry R Witness J) → Table R Witness J
  | none => table
  | some entry => insert table entry

def fold {α : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → Option (Entry R Witness J)) : List α → Table R Witness J → Table R Witness J
  | [],table => table
  | a::rest,table => fold evaluate rest (applyEntry table (evaluate a))

theorem best_congr {Witness : Type*} (P Q : Selection R Witness → Prop) (value : Option (Selection R Witness))
    (h : ∀ chosen, P chosen↔Q chosen) (hBest : Best P value) : Best Q value := by
  cases value with
  | none => exact fun chosen hc => hBest chosen ((h chosen).mpr hc)
  | some chosen => exact ⟨(h chosen).mp hBest.1,fun other ho => hBest.2 other ((h other).mpr ho)⟩

theorem empty_best (Witness : Type*) (J : ℕ) (i : Fin J) : Best (fun _ : Selection R Witness => False) ((empty Witness J).read i) := by
  rw [empty,FixedArrayTable.read_ofFn]
  exact fun _ h => h

theorem insert_best {Witness : Type*} {J : ℕ} (table : Table R Witness J) (entry : Entry R Witness J)
    (possible : Fin J → Selection R Witness → Prop) (hBest : ∀ i, Best (possible i) (table.read i)) (i : Fin J) :
    Best (fun chosen => possible i chosen ∨ (i=entry.label ∧ chosen=entry.selection)) ((insert table entry).read i) := by
  unfold insert
  rw [FixedArrayTable.read_write]
  by_cases hi : i=entry.label
  · subst i
    rw [if_pos rfl]
    have he := pick_best (possible entry.label) (fun chosen => chosen=entry.selection)
      (table.read entry.label) (some entry.selection) (hBest _) ⟨rfl,by intro other ho; subst other; exact le_rfl⟩
    exact best_congr _ _ _ (by intro chosen; simp) he
  · rw [if_neg hi]
    exact best_congr _ _ _ (by intro chosen; simp only [hi,false_and,or_false]) (hBest i)

theorem apply_best {Witness : Type*} {J : ℕ} (table : Table R Witness J) (entry : Option (Entry R Witness J))
    (possible : Fin J → Selection R Witness → Prop) (hBest : ∀ i, Best (possible i) (table.read i)) (i : Fin J) :
    Best (fun chosen => possible i chosen ∨ entry=some ⟨i,chosen⟩) ((applyEntry table entry).read i) := by
  cases entry with
  | none => exact best_congr _ _ _ (by intro chosen; simp) (hBest i)
  | some entry =>
    exact best_congr _ _ _ (by
      intro chosen
      cases entry
      simp only [Option.some.injEq,Entry.mk.injEq]
      exact or_congr Iff.rfl (and_congr eq_comm eq_comm))
      (insert_best table entry possible hBest i)

theorem fold_best {α : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → Option (Entry R Witness J)) (xs : List α) (table : Table R Witness J)
    (possible : Fin J → Selection R Witness → Prop) (hBest : ∀ i, Best (possible i) (table.read i)) (i : Fin J) :
    Best (fun chosen => possible i chosen ∨ ∃ a∈xs, evaluate a=some ⟨i,chosen⟩) ((fold evaluate xs table).read i) := by
  induction xs generalizing table possible with
  | nil => exact best_congr _ _ _ (by intro chosen; simp) (hBest i)
  | cons a rest ih =>
    have he := ih (applyEntry table (evaluate a))
      (fun j chosen => possible j chosen ∨ evaluate a=some ⟨j,chosen⟩) (apply_best table (evaluate a) possible hBest)
    exact best_congr _ _ _ (by intro chosen; simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left,or_assoc]) he

theorem fold_empty_best {α : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → Option (Entry R Witness J)) (xs : List α) (i : Fin J) :
    Best (fun chosen => ∃ a∈xs, evaluate a=some ⟨i,chosen⟩) ((fold evaluate xs (empty Witness J)).read i) :=
  best_congr _ _ _ (by intro chosen; simp) (fold_best evaluate xs (empty Witness J) (fun _ _ => False) (empty_best Witness J) i)

def rows {α β : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → β → Option (Entry R Witness J)) (columns : List β) :
    List α → Table R Witness J → Table R Witness J
  | [],table => table
  | a::rest,table => rows evaluate columns rest (fold (evaluate a) columns table)

theorem rows_best {α β : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → β → Option (Entry R Witness J))
    (columns : List β) (xs : List α) (table : Table R Witness J)
    (possible : Fin J → Selection R Witness → Prop) (hBest : ∀ i, Best (possible i) (table.read i)) (i : Fin J) :
    Best (fun chosen => possible i chosen ∨ ∃ a∈xs, ∃ b∈columns, evaluate a b=some ⟨i,chosen⟩)
      ((rows evaluate columns xs table).read i) := by
  induction xs generalizing table possible with
  | nil => exact best_congr _ _ _ (by intro chosen; simp) (hBest i)
  | cons a rest ih =>
    have he := ih (fold (evaluate a) columns table)
      (fun j chosen => possible j chosen ∨ ∃ b∈columns, evaluate a b=some ⟨j,chosen⟩)
      (fold_best (evaluate a) columns table possible hBest)
    exact best_congr _ _ _ (by intro chosen; simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left,or_assoc]) he

theorem rows_empty_best {α β : Type*} {Witness : Type*} {J : ℕ} (evaluate : α → β → Option (Entry R Witness J))
    (columns : List β) (xs : List α) (i : Fin J) :
    Best (fun chosen => ∃ a∈xs, ∃ b∈columns, evaluate a b=some ⟨i,chosen⟩)
      ((rows evaluate columns xs (empty Witness J)).read i) :=
  best_congr _ _ _ (by intro chosen; simp) (rows_best evaluate columns xs (empty Witness J) (fun _ _ => False) (empty_best Witness J) i)

end Blotto.GeneralPaperOrderedProfitScatter
