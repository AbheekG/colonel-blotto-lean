import Blotto.GeneralPaperProfitScatter

/-! Actual balanced profit-grid DP with exact rational resource tags and
typed predecessor indices. Children are computed once and retained for
backtracking. Merge pairs stream directly into one native output table.
-/
namespace Blotto.GeneralPaperBalancedProfitDP
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperResourceMinimum GeneralPaperProfitScatter
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev Field (K : ℕ) := FixedArrayTable K (ℕ × ℚ)

inductive Tree (K : ℕ) : ℕ → Type
  | leaf (field : Field K) : Tree K 0
  | node {h : ℕ} (left right : Tree K h) : Tree K (h+1)

def Trace (K J : ℕ) : ℕ → Type
  | 0 => Fin K
  | _+1 => Fin J × Fin J

inductive Computation (K J : ℕ) : ℕ → Type
  | leaf (states : Table (Fin K) J) : Computation K J 0
  | node {h : ℕ} (left right : Computation K J h) (states : Table (Fin J × Fin J) J) : Computation K J (h+1)

def Computation.table {K J : ℕ} : {h : ℕ} → Computation K J h → Table (Trace K J h) J
  | _,.leaf states => states
  | _,.node _ _ states => states

def leafEntry {K q w B : ℕ} (grid : Prepared q w B) (field : Field K) (a : Fin K) : Entry (Fin K) grid.size :=
  ⟨(GeneralPaperProfitGridRound.leaf grid (field.read a).1).label,⟨(field.read a).2,a⟩⟩

def leafTable {K q w B : ℕ} (grid : Prepared q w B) (field : Field K) : Table (Fin K) grid.size :=
  fold (fun a => some (leafEntry grid field a)) (List.finRange K) (empty _ _)

def mergeEntry {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table Left grid.size) (right : Table Right grid.size) (i j : Fin grid.size) :
    Option (Entry (Fin grid.size × Fin grid.size) grid.size) :=
  match left.read i,right.read j with
  | some a,some b => some ⟨(GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label,
      ⟨a.cost+b.cost,(i,j)⟩⟩
  | _,_ => none

def mergeTable {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table Left grid.size) (right : Table Right grid.size) : Table (Fin grid.size × Fin grid.size) grid.size :=
  rows (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) (empty _ _)

def run {K q w B : ℕ} (grid : Prepared q w B) : {h : ℕ} → Tree K h → Computation K grid.size h
  | _,.leaf field => .leaf (leafTable grid field)
  | _,.node left right =>
    let lc := run grid left
    let rc := run grid right
    .node lc rc (mergeTable grid lc.table rc.table)

def decode {K J : ℕ} : {h : ℕ} → Computation K J h → Fin J → Option (List (Fin K))
  | _,.leaf states,label => (states.read label).map (fun chosen => [chosen.predecessor])
  | _,.node left right states,label =>
    match states.read label with
    | none => none
    | some chosen => do
      let ll ← decode left chosen.predecessor.1
      let rr ← decode right chosen.predecessor.2
      pure (ll++rr)

def LeafPossible {K q w B : ℕ} (grid : Prepared q w B) (field : Field K) (label : Fin grid.size) (chosen : Selection (Fin K)) : Prop :=
  ∃ a, some (leafEntry grid field a)=some ⟨label,chosen⟩

def MergePossible {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table Left grid.size) (right : Table Right grid.size) (label : Fin grid.size)
    (chosen : Selection (Fin grid.size × Fin grid.size)) : Prop :=
  ∃ i j, mergeEntry grid left right i j=some ⟨label,chosen⟩

theorem leaf_best {K q w B : ℕ} (grid : Prepared q w B) (field : Field K) (label : Fin grid.size) :
    Best (LeafPossible grid field label) ((leafTable grid field).read label) := by
  change Best (fun chosen => ∃ a, some (leafEntry grid field a)=some ⟨label,chosen⟩)
    ((fold (fun a => some (leafEntry grid field a)) (List.finRange K) (empty _ _)).read label)
  simpa only [List.mem_finRange,true_and] using
    fold_empty_best (fun a => some (leafEntry grid field a)) (List.finRange K) label

theorem merge_best {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table Left grid.size) (right : Table Right grid.size) (label : Fin grid.size) :
    Best (MergePossible grid left right label) ((mergeTable grid left right).read label) := by
  change Best (fun chosen => ∃ i j, mergeEntry grid left right i j=some ⟨label,chosen⟩)
    ((rows (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) (empty _ _)).read label)
  simpa only [List.mem_finRange,true_and] using
    rows_empty_best (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) label

theorem leaf_description {K q w B : ℕ} (grid : Prepared q w B) (field : Field K) (label : Fin grid.size)
    (chosen : Selection (Fin K)) (hRead : (leafTable grid field).read label=some chosen) :
    ∃ a, chosen=⟨(field.read a).2,a⟩ ∧ (GeneralPaperProfitGridRound.leaf grid (field.read a).1).label=label := by
  have he := leaf_best grid field label
  rw [hRead] at he
  obtain ⟨a,ha⟩ := he.1
  have hs := congrArg Entry.selection (Option.some.inj ha)
  have hl := congrArg Entry.label (Option.some.inj ha)
  exact ⟨a,hs.symm,hl⟩

theorem merge_description {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table Left grid.size) (right : Table Right grid.size) (label : Fin grid.size)
    (chosen : Selection (Fin grid.size × Fin grid.size)) (hRead : (mergeTable grid left right).read label=some chosen) :
    ∃ i j a b, left.read i=some a ∧ right.read j=some b ∧ chosen=⟨a.cost+b.cost,(i,j)⟩ ∧
      (GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label=label := by
  have he := merge_best grid left right label
  rw [hRead] at he
  obtain ⟨i,j,hij⟩ := he.1
  cases hl : left.read i with
  | none => simp [mergeEntry,hl] at hij
  | some a =>
    cases hr : right.read j with
    | none => simp [mergeEntry,hl,hr] at hij
    | some b =>
      simp only [mergeEntry,hl,hr] at hij
      have hs := congrArg Entry.selection (Option.some.inj hij)
      have ht := congrArg Entry.label (Option.some.inj hij)
      exact ⟨i,j,a,b,hl,hr,hs.symm,ht⟩

end Blotto.GeneralPaperBalancedProfitDP
