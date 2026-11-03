import Blotto.GeneralPaperBalancedProfitSound

/-! The root scans native states for the highest exact-budget-feasible
profit label, then follows its stored predecessors. No resource is rounded.
Approximation/dominance and the actual physical-option catalogue are separate
joins; the soundness theorem already establishes a complete tagged tuple.
-/
namespace Blotto.GeneralPaperProfitRoot
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperResourceMinimum
open GeneralPaperProfitScatter GeneralPaperBalancedProfitDP GeneralPaperBalancedProfitSound
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Highest {J : ℕ} (possible : Fin J → Prop) : Option (Fin J) → Prop
  | none => ∀ i, ¬possible i
  | some chosen => possible chosen ∧ ∀ i, possible i → i≤chosen

def pick {J : ℕ} : Option (Fin J) → Option (Fin J) → Option (Fin J)
  | none,b => b
  | a,none => a
  | some a,some b => if a≤b then some b else some a

theorem highest_congr {J : ℕ} (P Q : Fin J → Prop) (value : Option (Fin J))
    (h : ∀ i, P i↔Q i) (hBest : Highest P value) : Highest Q value := by
  cases value with
  | none => exact fun i hi => hBest i ((h i).mpr hi)
  | some chosen => exact ⟨(h chosen).mp hBest.1,fun i hi => hBest.2 i ((h i).mpr hi)⟩

theorem pick_highest {J : ℕ} (P Q : Fin J → Prop) (a b : Option (Fin J))
    (ha : Highest P a) (hb : Highest Q b) : Highest (fun i => P i ∨ Q i) (pick a b) := by
  cases a with
  | none =>
    cases b with
    | none => exact fun i hi => hi.elim (ha i) (hb i)
    | some b => exact ⟨Or.inr hb.1,fun i hi => hi.elim (fun h => (ha i h).elim) (hb.2 i)⟩
  | some a =>
    cases b with
    | none => exact ⟨Or.inl ha.1,fun i hi => hi.elim (ha.2 i) (fun h => (hb i h).elim)⟩
    | some b =>
      change Highest _ (if a≤b then some b else some a)
      split
      · rename_i hab
        exact ⟨Or.inr hb.1,fun i hi => hi.elim (fun h => (ha.2 i h).trans hab) (hb.2 i)⟩
      · rename_i hab
        exact ⟨Or.inl ha.1,fun i hi => hi.elim (ha.2 i) (fun h => (hb.2 i h).trans (le_of_not_ge hab))⟩

theorem singleton_highest {J : ℕ} (value : Option (Fin J)) : Highest (fun i => value=some i) value := by
  cases value with
  | none => exact fun i hi => by cases hi
  | some chosen => exact ⟨rfl,fun i hi => by have he := Option.some.inj hi; subst i; exact le_rfl⟩

def scan {α : Type*} {J : ℕ} (evaluate : α → Option (Fin J)) : List α → Option (Fin J)
  | [] => none
  | a::rest => pick (evaluate a) (scan evaluate rest)

theorem scan_highest {α : Type*} {J : ℕ} (evaluate : α → Option (Fin J)) (xs : List α) :
    Highest (fun i => ∃ a∈xs, evaluate a=some i) (scan evaluate xs) := by
  induction xs with
  | nil => simp [scan,Highest]
  | cons a rest ih =>
    exact highest_congr _ _ _
      (by intro i; simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left])
      (pick_highest _ _ _ _ (singleton_highest (evaluate a)) ih)

def Feasible {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i : Fin J) : Prop :=
  ∃ chosen, table.read i=some chosen ∧ chosen.cost≤budget

def eligible {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i : Fin J) : Option (Fin J) :=
  match table.read i with
  | none => none
  | some chosen => if chosen.cost≤budget then some i else none

theorem eligible_iff {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i j : Fin J) :
    eligible table budget i=some j ↔ j=i ∧ Feasible table budget i := by
  cases hr : table.read i with
  | none => simp [eligible,Feasible,hr]
  | some chosen =>
    by_cases hc : chosen.cost≤budget
    <;> simp [eligible,Feasible,hr,hc,eq_comm]

def select {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) : Option (Fin J) :=
  scan (eligible table budget) (List.finRange J)

theorem select_highest {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) :
    Highest (Feasible table budget) (select table budget) := by
  exact highest_congr _ _ _ (by intro i; simp [eligible_iff]) (scan_highest (eligible table budget) (List.finRange J))

theorem select_read {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i : Fin J)
    (hSelect : select table budget=some i) : Feasible table budget i := by
  have he := select_highest table budget
  rw [hSelect] at he
  exact he.1

theorem select_maximal {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i : Fin J)
    (hSelect : select table budget=some i) (j : Fin J) (hJ : Feasible table budget j) : j≤ i := by
  have he := select_highest table budget
  rw [hSelect] at he
  exact he.2 j hJ

theorem select_success {Witness : Type*} {J : ℕ} (table : Table Witness J) (budget : ℚ) (i : Fin J) (hI : Feasible table budget i) :
    ∃ j, select table budget=some j := by
  have he := select_highest table budget
  cases hs : select table budget with
  | none => rw [hs] at he; exact (he i hI).elim
  | some j => exact ⟨j,rfl⟩

def solve {K h q w B : ℕ} (grid : Prepared q w B) (tree : Tree K h) (budget : ℚ) :
    Option (Fin grid.size × List (Fin K)) :=
  let computed := run grid tree
  match select computed.table budget with
  | none => none
  | some label => (decode computed label).map (fun labels => (label,labels))

theorem solve_sound {K h q w B : ℕ} (tree : Tree K h) (budget : ℚ) (label : Fin (prepare q w B).size) (labels : List (Fin K))
    (hSolve : solve (prepare q w B) tree budget=some (label,labels)) :
    ∃ cost profit, Realizes tree labels cost profit ∧ cost≤budget ∧ q*(prepare q w B).numerators.read label≤profit*denominator w B := by
  dsimp only [solve] at hSolve
  cases hs : select (run (prepare q w B) tree).table budget with
  | none => simp only [hs] at hSolve; cases hSolve
  | some selected =>
    obtain ⟨chosen,hr,hBudget⟩ := select_read _ budget selected hs
    obtain ⟨ll,profit,hd,hReal,hProfit⟩ := state_sound tree selected chosen hr
    simp only [hs,hd,Option.map_some] at hSolve
    have he := Option.some.inj hSolve
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨chosen.cost,profit,hReal,hBudget,hProfit⟩

theorem solve_success {K h q w B : ℕ} (tree : Tree K h) (budget : ℚ) (i : Fin (prepare q w B).size)
    (hI : Feasible (run (prepare q w B) tree).table budget i) :
    ∃ label labels, solve (prepare q w B) tree budget=some (label,labels) := by
  obtain ⟨label,hs⟩ := select_success _ budget i hI
  obtain ⟨chosen,hr,_⟩ := select_read _ budget label hs
  obtain ⟨labels,profit,hd,_,_⟩ := state_sound tree label chosen hr
  exact ⟨label,labels,by simp only [solve,hs,hd,Option.map_some]⟩

end Blotto.GeneralPaperProfitRoot
