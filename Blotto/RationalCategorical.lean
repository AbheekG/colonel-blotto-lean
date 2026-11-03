import Blotto.ProbabilityWords
import Blotto.WordMachineLaw
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Native categorical control flow from nonnegative rational weights. The
remaining list is shared; each request uses its head weight divided by the
remaining mass and completes at most one list position. Zero-mass states have
an explicit deterministic outcome for totality. -/

namespace Blotto

structure RationalWeightList (α : Type*) where
  items : List (α × ℚ)
  nonnegative : ∀ item ∈ items, 0 ≤ item.2

namespace RationalWeightList

def mass {α : Type*} (l : RationalWeightList α) : ℚ := (l.items.map Prod.snd).sum

theorem mass_nonnegative {α : Type*} (l : RationalWeightList α) : 0 ≤ l.mass := by
  apply List.sum_nonneg
  intro q hq
  rcases List.mem_map.mp hq with ⟨item, hi, rfl⟩
  exact l.nonnegative item hi

def weightedSum {α : Type*} (l : RationalWeightList α) (f : α → ℝ) : ℝ :=
  (l.items.map (fun item => (item.2 : ℝ) * f item.1)).sum

end RationalWeightList

inductive CategoricalState (α : Type*) where
  | remaining (items : RationalWeightList α)
  | selected (value : α)

def categoricalTransition {α : Type*} (fallback : α) (cursor : CategoricalState α) : WordTransition (CategoricalState α) α := by
  cases cursor with
  | selected value => exact .done value
  | remaining l =>
    cases l with
    | mk items hn =>
      cases items with
      | nil => exact .done fallback
      | cons head rest =>
        cases rest with
        | nil => exact .done head.1
        | cons next tail =>
          let l : RationalWeightList α := ⟨head :: next :: tail, hn⟩
          let t : RationalWeightList α := ⟨next :: tail, fun item hi => hn item (by simp [hi])⟩
          by_cases hm : 0 < l.mass
          · have hh : 0 ≤ head.2 := hn head (by simp)
            have hle : head.2 ≤ l.mass := by
              change head.2 ≤ head.2 + t.mass
              linarith [t.mass_nonnegative]
            let w := ProbabilityWords.ofRat (head.2 / l.mass) ⟨div_nonneg hh (le_of_lt hm), (div_le_one hm).mpr hle⟩
            exact .ask w.numerator w.denominator w.denominator_pos w.normalized
              (.selected head.1) (.remaining t)
          · exact .done head.1

def categoricalRank {α : Type*} : CategoricalState α → ℕ
  | .selected _ => 0
  | .remaining l => l.items.length - 1

def categoricalMachine {α : Type*} (fallback : α) : WordStateMachine (CategoricalState α) α where
  step := categoricalTransition fallback
  rank := categoricalRank
  progress := by
    intro cursor
    cases cursor with
    | selected value => trivial
    | remaining l =>
      cases l with
      | mk items hn =>
        cases items with
        | nil => trivial
        | cons head rest =>
          cases rest with
          | nil => trivial
          | cons next tail =>
            unfold categoricalTransition
            dsimp only
            split_ifs
            · change 0 < (head :: next :: tail).length - 1 ∧ (next :: tail).length - 1 < (head :: next :: tail).length - 1
              simp
            · trivial

end Blotto
