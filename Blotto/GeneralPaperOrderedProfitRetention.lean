import Blotto.GeneralPaperOrderedProfitRoot

/-! Minimum-table retention preserves feasibility without rounding resource
tags. Any actual feasible tuple supplies a reachable feasible root state;
in particular the catalogue's zero-resource choices guarantee success.
Relative profit dominance is still a separate required theorem.
-/
namespace Blotto.GeneralPaperOrderedProfitRetention
open GeneralPaperProfitGridPrepare GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

theorem leaf_retained {K q w B : ℕ} (grid : Prepared q w B) (field : Field R K) (a : Fin K) :
    ∃ chosen, (leafTable grid field).read (GeneralPaperProfitGridRound.leaf grid (field.read a).1).label=some chosen ∧
      chosen.cost≤(field.read a).2 := by
  let entry := leafEntry grid field a
  have hp : LeafPossible grid field entry.label entry.selection := ⟨a,rfl⟩
  have hb := leaf_best grid field entry.label
  cases hr : (leafTable grid field).read entry.label with
  | none => rw [hr] at hb; exact (hb entry.selection hp).elim
  | some chosen =>
    rw [hr] at hb
    exact ⟨chosen,hr,hb.2 entry.selection hp⟩

theorem merge_retained {Left Right : Type*} {q w B : ℕ} (grid : Prepared q w B)
    (left : Table R Left grid.size) (right : Table R Right grid.size) (i j : Fin grid.size)
    (a : Selection R Left) (b : Selection R Right) (hl : left.read i=some a) (hr : right.read j=some b) :
    ∃ chosen, (mergeTable grid left right).read
        (GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label=some chosen ∧
      chosen.cost≤a.cost+b.cost := by
  let label := (GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label
  let candidate : Selection R (Fin grid.size × Fin grid.size) := ⟨a.cost+b.cost,(i,j)⟩
  have hp : MergePossible grid left right label candidate := ⟨i,j,by simp only [mergeEntry,hl,hr]; rfl⟩
  have hb := merge_best grid left right label
  cases hs : (mergeTable grid left right).read label with
  | none => rw [hs] at hb; exact (hb candidate hp).elim
  | some chosen =>
    rw [hs] at hb
    exact ⟨chosen,rfl,hb.2 candidate hp⟩

theorem resource_dominance {K h q w B : ℕ} (grid : Prepared q w B) (tree : Tree R K h)
    (labels : List (Fin K)) (cost : R) (profit : ℕ) (hRealizes : Realizes tree labels cost profit) :
    ∃ label chosen, (run grid tree).table.read label=some chosen ∧ chosen.cost≤cost := by
  induction tree generalizing labels cost profit with
  | leaf field =>
    obtain ⟨a,rfl,rfl,rfl⟩ := hRealizes
    obtain ⟨chosen,hr,hCost⟩ := leaf_retained grid field a
    exact ⟨(GeneralPaperProfitGridRound.leaf grid (field.read a).1).label,chosen,hr,hCost⟩
  | @node h left right ihl ihr =>
    obtain ⟨ll,lc,lp,rr,rc,rp,hl,hr,rfl,rfl,rfl⟩ := hRealizes
    obtain ⟨i,a,ha,hca⟩ := ihl ll lc lp hl
    obtain ⟨j,b,hb,hcb⟩ := ihr rr rc rp hr
    obtain ⟨chosen,hRead,hCost⟩ := merge_retained grid (run grid left).table (run grid right).table i j a b ha hb
    exact ⟨(GeneralPaperProfitGridRound.merge grid (grid.numerators.read i+grid.numerators.read j)).label,
      chosen,hRead,hCost.trans (add_le_add hca hcb)⟩

theorem feasible_success {K h q w B : ℕ} (tree : Tree R K h) (labels : List (Fin K)) (cost budget : R) (profit : ℕ)
    (hRealizes : Realizes tree labels cost profit) (hBudget : cost≤budget) :
    ∃ label output, GeneralPaperOrderedProfitRoot.solve (prepare q w B) tree budget=some (label,output) := by
  obtain ⟨label,chosen,hr,hCost⟩ := resource_dominance (prepare q w B) tree labels cost profit hRealizes
  exact GeneralPaperOrderedProfitRoot.solve_success tree budget label ⟨chosen,hr,hCost.trans hBudget⟩

def ZeroResource {K : ℕ} : {h : ℕ} → Tree R K h → Prop
  | _,.leaf field => ∃ a, (field.read a).2=0
  | _,.node left right => ZeroResource left ∧ ZeroResource right

theorem zero_realizes {K h : ℕ} (tree : Tree R K h) (hZero : ZeroResource tree) :
    ∃ labels profit, Realizes tree labels 0 profit := by
  induction tree with
  | leaf field =>
    obtain ⟨a,ha⟩ := hZero
    exact ⟨[a],(field.read a).1,a,rfl,ha.symm,rfl⟩
  | node left right ihl ihr =>
    obtain ⟨ll,lp,hl⟩ := ihl hZero.1
    obtain ⟨rr,rp,hr⟩ := ihr hZero.2
    exact ⟨ll++rr,lp+rp,ll,0,lp,rr,0,rp,hl,hr,rfl,by simp,rfl⟩

theorem zero_success {K h q w B : ℕ} (tree : Tree R K h) (budget : R) (hZero : ZeroResource tree) (hBudget : 0≤budget) :
    ∃ label output, GeneralPaperOrderedProfitRoot.solve (prepare q w B) tree budget=some (label,output) := by
  obtain ⟨labels,profit,hr⟩ := zero_realizes tree hZero
  exact feasible_success tree labels 0 budget profit hr hBudget

end Blotto.GeneralPaperOrderedProfitRetention
