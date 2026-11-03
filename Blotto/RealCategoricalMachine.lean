import Blotto.RealStateMachineRefinement
import Blotto.RealCategoricalProgram

/-! Exact categorical control retains the remaining mass, updating it by one
subtraction. No suffix sum is recomputed on a request. Zero-mass states have
an explicit deterministic branch. -/

namespace Blotto
open scoped Classical

structure RealWeightList (α : Type*) where
  items : List (α × ℝ)
  mass : ℝ
  mass_eq : mass = (items.map Prod.snd).sum
  nonnegative : ∀ item ∈ items, 0 ≤ item.2

namespace RealWeightList

noncomputable def prepare {α : Type*} (items : List (α × ℝ)) (h : ∀ item ∈ items, 0 ≤ item.2) : RealWeightList α :=
  ⟨items, (items.map Prod.snd).sum, rfl, h⟩

theorem mass_nonnegative {α : Type*} (l : RealWeightList α) : 0 ≤ l.mass := by
  rw [l.mass_eq]
  apply List.sum_nonneg
  intro w hw
  rcases List.mem_map.mp hw with ⟨item, hi, rfl⟩
  exact l.nonnegative item hi

noncomputable def tail {α : Type*} (l : RealWeightList α) (head : α × ℝ) (rest : List (α × ℝ))
    (h : l.items = head :: rest) : RealWeightList α where
  items := rest
  mass := l.mass - head.2
  mass_eq := by rw [l.mass_eq, h]; simp
  nonnegative := fun item hi => l.nonnegative item (by rw [h]; simp [hi])

end RealWeightList

inductive RealCategoricalState (α : Type*) where
  | remaining (weights : RealWeightList α)
  | selected (value : α)

noncomputable def realCategoricalStepReference {α : Type*} (fallback : α) :
    RealCategoricalState α → RealTransition (RealCategoricalState α) α
  | .selected value => .done value
  | .remaining ⟨[], _, _, _⟩ => .done fallback
  | .remaining ⟨[head], _, _, _⟩ => .done head.1
  | .remaining ⟨head :: next :: tail, mass, hEq, hn⟩ =>
    let l : RealWeightList α := ⟨head :: next :: tail, mass, hEq, hn⟩
    let t := l.tail head (next :: tail) rfl
    if hm : 0 < mass then
      .ask (head.2 / mass)
        ⟨div_nonneg (hn head (by simp)) hm.le,
          (div_le_one hm).mpr (by
            have hNonneg := t.mass_nonnegative
            change 0 ≤ mass - head.2 at hNonneg
            linarith)⟩
        (.selected head.1) (.remaining t)
    else .done head.1

noncomputable def realCategoricalStep {α : Type*} (fallback : α) :
    RealCategoricalState α → RealTransition (RealCategoricalState α) α
  | .selected value => .done value
  | .remaining ⟨[], _, _, _⟩ => .done fallback
  | .remaining ⟨[head], _, _, _⟩ => .done head.1
  | .remaining ⟨head :: next :: tail, mass, hEq, hn⟩ =>
    if hm : 0 < mass then
      let registers := RealCategoricalProgram.run head.2 mass
      let t : RealWeightList α :=
        { items := next :: tail
          mass := registers.getD 2 0
          mass_eq := by
            rw [RealCategoricalProgram.run_nextMass]
            have he := hEq
            simp only [List.map_cons, List.sum_cons] at he ⊢
            linarith
          nonnegative := fun item hi => hn item (by simp [hi]) }
      .ask (registers.getD 3 0)
        (by
          rw [RealCategoricalProgram.run_probability]
          refine ⟨div_nonneg (hn head (by simp)) hm.le, (div_le_one hm).mpr ?_⟩
          have hNonneg := t.mass_nonnegative
          change 0 ≤ registers.getD 2 0 at hNonneg
          rw [RealCategoricalProgram.run_nextMass] at hNonneg
          linarith)
        (.selected head.1) (.remaining t)
    else .done head.1

theorem realCategoricalStep_refines {α : Type*} (fallback : α) (cursor : RealCategoricalState α) :
    realCategoricalStep fallback cursor = realCategoricalStepReference fallback cursor := by
  cases cursor with
  | selected value => rfl
  | remaining l =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil => rfl
      | cons head rest =>
        cases rest with
        | nil => rfl
        | cons next tail =>
          simp only [realCategoricalStep, realCategoricalStepReference]
          by_cases hm : 0 < mass
          · simp only [dite_eq_left hm, RealCategoricalProgram.run_nextMass,
              RealCategoricalProgram.run_probability]
            rfl
          · simp only [dite_eq_right hm]


def realCategoricalRank {α : Type*} : RealCategoricalState α → ℕ
  | .selected _ => 0
  | .remaining l => l.items.length - 1

noncomputable def realCategoricalMachine {α : Type*} (fallback : α) : RealStateMachine (RealCategoricalState α) α where
  step := realCategoricalStep fallback
  rank := realCategoricalRank
  progress := by
    intro cursor
    cases cursor with
    | selected value => trivial
    | remaining l =>
      cases l with
      | mk items mass hEq hn =>
        cases items with
        | nil => trivial
        | cons head rest =>
          cases rest with
          | nil => trivial
          | cons next tail =>
            rw [realCategoricalStep_refines]
            unfold realCategoricalStepReference
            dsimp only
            by_cases hm : 0 < mass
            · rw [dite_eq_left hm]
              change 0 < (head :: next :: tail).length - 1 ∧
                (next :: tail).length - 1 < (head :: next :: tail).length - 1
              simp
            · rw [dite_eq_right hm]
              trivial

end Blotto
