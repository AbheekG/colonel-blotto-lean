import Blotto.RealStateMachineRefinement
import Blotto.RealStateMachineCounts
import Blotto.ResourceRounding

/-! Real resource rounding follows one indexed state path. Its finite tree
is the retained rounding semantics, with no tree construction in the runtime. -/

namespace Blotto
open scoped Classical

namespace RoundingTree

noncomputable def realChoice {n : ℕ} : RoundingTree n → RealChoiceTree (Allocation n)
  | .leaf r => .leaf r
  | .fork p hp upper lower => .fork p hp upper.realChoice lower.realChoice

theorem realChoice_height {n : ℕ} (T : RoundingTree n) : T.realChoice.height = T.height := by
  induction T with
  | leaf r => rfl
  | fork p hp upper lower ihUpper ihLower => simp [realChoice, RealChoiceTree.height, height, ihUpper, ihLower]

theorem realChoice_forLeaves {n : ℕ} (T : RoundingTree n) (P : Allocation n → Prop) :
    T.realChoice.ForLeaves P ↔ T.ForLeaves P := by
  induction T with
  | leaf r => rfl
  | fork p hp upper lower ihUpper ihLower =>
    simp only [realChoice, RealChoiceTree.ForLeaves, ForLeaves, ihUpper, ihLower]

end RoundingTree

noncomputable def realResourceStep {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource) :
    (ℕ × Allocation n) → RealTransition (ℕ × Allocation n) (Allocation n)
  | (0, resource) => .done resource
  | (fuel + 1, resource) =>
    if h : 1 < (fractionalSet length resource).card then
      let c := select resource h
      let r := resourcePair length resource c.i c.j c.interior_i c.interior_j
      .ask r.probability ⟨r.probability_pos.le, r.probability_lt_one.le⟩
        (fuel, updatePair resource c.i c.j r.upper) (fuel, updatePair resource c.i c.j r.lower)
    else .done resource

noncomputable def realResourceMachine {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource) :
    RealStateMachine (ℕ × Allocation n) (Allocation n) where
  step := realResourceStep length select
  rank := Prod.fst
  progress := by
    rintro ⟨fuel, resource⟩
    cases fuel with
    | zero => trivial
    | succ fuel =>
      unfold realResourceStep
      dsimp only
      by_cases h : 1 < (fractionalSet length resource).card
      · rw [dite_eq_left h]
        change fuel < fuel + 1 ∧ fuel < fuel + 1
        omega
      · rw [dite_eq_right h]
        trivial

theorem realResourceMachine_specification {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource)
    (fuel : ℕ) (resource : Allocation n) :
    (realResourceMachine length select).specification (fuel, resource) =
      (roundResources length select fuel resource).realChoice := by
  induction fuel generalizing resource with
  | zero =>
    rw [(realResourceMachine length select).specification_done _ resource rfl]
    rfl
  | succ fuel ih =>
    conv_lhs => unfold RealStateMachine.specification
    simp only [realResourceMachine, realResourceStep]
    conv_rhs => unfold roundResources
    by_cases h : 1 < (fractionalSet length resource).card
    · rw [dite_eq_left h, dite_eq_left h]
      let c := select resource h
      let r := resourcePair length resource c.i c.j c.interior_i c.interior_j
      change RealChoiceTree.fork r.probability _
        ((realResourceMachine length select).specification (fuel, updatePair resource c.i c.j r.upper))
        ((realResourceMachine length select).specification (fuel, updatePair resource c.i c.j r.lower)) = _
      rw [ih, ih]
      rfl
    · rw [dite_eq_right h, dite_eq_right h]
      rfl

namespace RealChoiceTree

theorem output_forLeaves_total {α : Type*} (T : RealChoiceTree α) (P : α → Prop)
    (hT : T.ForLeaves P) (C : ℕ) (fallback : α) (seed : Fin C → ℝ) (hC : T.height ≤ C) :
    P (T.output C fallback seed) := by
  have hSome := T.sample_total C seed hC
  unfold output
  cases hResult : (T.sample C seed).1 with
  | none => exact False.elim (hSome hResult)
  | some x => exact T.sample_forLeaves P hT C seed hResult

end RealChoiceTree
end Blotto
