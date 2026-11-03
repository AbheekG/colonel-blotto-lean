import Blotto.RealCategoricalLaw

/-! A head/tail reference expression exposes the measurability of varying
real tables. The primary runtime remains the fixed-reader indexed machine. -/

namespace Blotto
open scoped Classical

noncomputable def realCategoricalReference {α : Type*} (fallback : α) :
    (C : ℕ) → List (α × ℝ) → ℝ → (Fin C → ℝ) → α
  | _, [], _, _ => fallback
  | _, [head], _, _ => head.1
  | 0, head :: _ :: _, mass, _ => if 0 < mass then fallback else head.1
  | C + 1, head :: next :: tail, mass, seed =>
    if 0 < mass then
      if seed 0 ≤ head.2 / mass then head.1
      else realCategoricalReference fallback C (next :: tail) (mass - head.2) (Fin.tail seed)
    else head.1

theorem realCategorical_selected_output {α : Type*} (fallback x : α) (C : ℕ) (seed : Fin C → ℝ) :
    ((realCategoricalMachine fallback).specification (.selected x)).output C fallback seed = x := by
  rw [(realCategoricalMachine fallback).specification_done _ x rfl]
  cases C <;> rfl

theorem realCategoricalReference_eq {α : Type*} (fallback : α) (C : ℕ) (l : RealWeightList α)
    (seed : Fin C → ℝ) :
    ((realCategoricalMachine fallback).specification (.remaining l)).output C fallback seed =
      realCategoricalReference fallback C l.items l.mass seed := by
  induction C generalizing l with
  | zero =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil =>
        rw [(realCategoricalMachine fallback).specification_done _ fallback rfl]
        rfl
      | cons head rest =>
        cases rest with
        | nil =>
          rw [(realCategoricalMachine fallback).specification_done _ head.1 rfl]
          rfl
        | cons next tail =>
          conv_lhs => unfold RealStateMachine.specification
          simp only [realCategoricalMachine, realCategoricalStep]
          by_cases hm : 0 < mass
          · rw [dite_eq_left hm]
            simp [RealChoiceTree.output, RealChoiceTree.sample, realCategoricalReference, hm]
          · rw [dite_eq_right hm]
            simp [RealChoiceTree.output, RealChoiceTree.sample, realCategoricalReference, hm]
  | succ C ih =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil =>
        rw [(realCategoricalMachine fallback).specification_done _ fallback rfl]
        rfl
      | cons head rest =>
        cases rest with
        | nil =>
          rw [(realCategoricalMachine fallback).specification_done _ head.1 rfl]
          rfl
        | cons next tail =>
          conv_lhs => unfold RealStateMachine.specification
          simp only [realCategoricalMachine, realCategoricalStep]
          by_cases hm : 0 < mass
          · rw [dite_eq_left hm, RealChoiceTree.output_fork_succ]
            change RealThresholdChoice.sample (head.2 / mass)
              (((realCategoricalMachine fallback).specification (.selected head.1)).output C fallback (Fin.tail seed))
              (((realCategoricalMachine fallback).specification
                (.remaining ((⟨head :: next :: tail, mass, hEq, hn⟩ : RealWeightList α).tail head (next :: tail) rfl))).output C fallback (Fin.tail seed))
              (seed 0) = _
            rw [realCategorical_selected_output]
            rw [ih]
            simp [RealThresholdChoice.sample, realCategoricalReference, hm, RealWeightList.tail]
          · rw [dite_eq_right hm]
            simp [RealChoiceTree.output, RealChoiceTree.sample, realCategoricalReference, hm]

theorem realCategorical_eq_reference {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j)
    (fallback : Fin k) (seed : Fin (k - 1) → ℝ) :
    realCategorical weight h fallback seed = realCategoricalReference fallback (k - 1)
      (List.ofFn fun j => (j, weight j)) (∑ j, weight j) seed := by
  change (realCategoricalMachine fallback).output (k - 1) (.remaining (realWeightTable weight h)) fallback seed = _
  rw [RealStateMachine.output_refines, realCategoricalReference_eq]
  rw [realWeightTable_mass]
  rfl

end Blotto
