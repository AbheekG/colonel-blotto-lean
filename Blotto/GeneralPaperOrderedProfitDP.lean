import Blotto.GeneralPaperOrderedProfitScatter

/-! Actual balanced profit-grid DP with exact ordered resource tags and
typed predecessor indices. Children are computed once and retained for
backtracking. Merge pairs stream directly into one native output table.
-/
namespace Blotto.GeneralPaperOrderedProfitDP
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

abbrev Field (R : Type) (K : ℕ) := FixedArrayTable K (ℕ × R)

inductive Tree (R : Type) (K : ℕ) : ℕ → Type
  | leaf (field : Field R K) : Tree R K 0
  | node {h : ℕ} (left right : Tree R K h) : Tree R K (h+1)

def Trace (K J : ℕ) : ℕ → Type
  | 0 => Fin K
  | _+1 => Fin J × Fin J

inductive Computation (R : Type) (K J : ℕ) : ℕ → Type
  | leaf (states : Table R (Fin K) J) : Computation R K J 0
  | node {h : ℕ} (left right : Computation R K J h) (states : Table R (Fin J × Fin J) J) : Computation R K J (h+1)

def Computation.table {K J : ℕ} : {h : ℕ} → Computation R K J h → Table R (Trace K J h) J
  | _,.leaf states => states
  | _,.node _ _ states => states

def leafEntry {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) (a : Fin K) : Entry R (Fin K) grid.size :=
  ⟨(GeneralPaperProfitGridRound.leaf grid (field.read a).1).label,⟨(field.read a).2,a⟩⟩

def leafTable {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) : Table R (Fin K) grid.size :=
  fold (fun a => some (leafEntry grid field a)) (List.finRange K) (empty _ _)

def mergeEntry {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) (i j : Fin grid.size) :
    Option (Entry R (Fin grid.size × Fin grid.size) grid.size) :=
  match left.read i,right.read j with
  | some a,some b => some ⟨(GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label,
      ⟨a.cost+b.cost,(i,j)⟩⟩
  | _,_ => none

def mergeTable {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) : Table R (Fin grid.size × Fin grid.size) grid.size :=
  rows (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) (empty _ _)

def run {K q w B : ℕ} (grid : Prepared q w B) : {h : ℕ} → Tree R K h → Computation R K grid.size h
  | _,.leaf field => .leaf (leafTable grid field)
  | _,.node left right =>
    let lc := run grid left
    let rc := run grid right
    .node lc rc (mergeTable grid lc.table rc.table)

def decode {K J : ℕ} : {h : ℕ} → Computation R K J h → Fin J → Option (List (Fin K))
  | _,.leaf states,label => (states.read label).map (fun chosen => [chosen.predecessor])
  | _,.node left right states,label =>
    match states.read label with
    | none => none
    | some chosen => do
      let ll ← decode left chosen.predecessor.1
      let rr ← decode right chosen.predecessor.2
      pure (ll++rr)

def LeafPossible {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) (label : Fin grid.size) (chosen : Selection R (Fin K)) : Prop :=
  ∃ a, some (leafEntry grid field a)=some ⟨label,chosen⟩

def MergePossible {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) (label : Fin grid.size)
    (chosen : Selection R (Fin grid.size × Fin grid.size)) : Prop :=
  ∃ i j, mergeEntry grid left right i j=some ⟨label,chosen⟩

theorem leaf_best {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) (label : Fin grid.size) :
    Best (LeafPossible grid field label) ((leafTable grid field).read label) := by
  change Best (fun chosen => ∃ a, some (leafEntry grid field a)=some ⟨label,chosen⟩)
    ((fold (fun a => some (leafEntry grid field a)) (List.finRange K) (empty _ _)).read label)
  simpa only [List.mem_finRange,true_and] using
    fold_empty_best (fun a => some (leafEntry grid field a)) (List.finRange K) label

theorem merge_best {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) (label : Fin grid.size) :
    Best (MergePossible grid left right label) ((mergeTable grid left right).read label) := by
  change Best (fun chosen => ∃ i j, mergeEntry grid left right i j=some ⟨label,chosen⟩)
    ((rows (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) (empty _ _)).read label)
  simpa only [List.mem_finRange,true_and] using
    rows_empty_best (mergeEntry grid left right) (List.finRange grid.size) (List.finRange grid.size) label

theorem leaf_description {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) (label : Fin grid.size)
    (chosen : Selection R (Fin K)) (hRead : (leafTable grid field).read label=some chosen) :
    ∃ a, chosen=⟨(field.read a).2,a⟩ ∧ (GeneralPaperProfitGridRound.leaf grid (field.read a).1).label=label := by
  have he := leaf_best grid field label
  rw [hRead] at he
  obtain ⟨a,ha⟩ := he.1
  have hs := congrArg Entry.selection (Option.some.inj ha)
  have hl := congrArg Entry.label (Option.some.inj ha)
  exact ⟨a,hs.symm,hl⟩

theorem merge_description {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) (label : Fin grid.size)
    (chosen : Selection R (Fin grid.size × Fin grid.size)) (hRead : (mergeTable grid left right).read label=some chosen) :
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

end Blotto.GeneralPaperOrderedProfitDP
