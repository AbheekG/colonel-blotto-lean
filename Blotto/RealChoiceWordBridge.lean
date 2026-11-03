import Blotto.RealStateMachineRefinement
import Blotto.WordTreeAllocationLaw
import Blotto.WordMachineSerialLaw

/-! Exact real threshold choices realize the same finite rational branch
weights as the word controller's ideal semantics. Only the random primitive
changes; state updates and outputs remain the original native ones. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical

namespace RealChoiceTree

noncomputable def mean {α : Type*} (f : α → ℝ) : RealChoiceTree α → ℝ
  | .leaf x => f x
  | .fork p _ upper lower => p * upper.mean f + (1 - p) * lower.mean f

theorem idealLaw_real_event {α : Type*} [MeasurableSpace α] (T : RealChoiceTree α) (A : Set α) (hA : MeasurableSet A) :
    (T.idealLaw : Measure α).real A = T.mean (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  induction T with
  | leaf x =>
    by_cases hx : x ∈ A <;> simp [idealLaw, RealThresholdChoice.pointLaw, mean, Measure.real, Measure.dirac_apply' _ hA, hx]
  | fork p hp upper lower hu hl =>
    rw [idealLaw, probabilityMixture_real_apply _ _ _ _ _ hA]
    simp [Fin.sum_univ_succ, mean]
    change p * (upper.idealLaw : Measure α).real A + (1 - p) * (lower.idealLaw : Measure α).real A = _
    rw [hu, hl]

end RealChoiceTree

namespace WordChoiceTree

noncomputable def realChoice {α : Type*} : WordChoiceTree α → RealChoiceTree α
  | .leaf x => .leaf x
  | .fork a b hb hab upper lower => .fork ((a : ℝ) / b)
      ⟨div_nonneg (Nat.cast_nonneg a) (by exact_mod_cast hb.le),
        (div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)⟩ upper.realChoice lower.realChoice

theorem realChoice_height {α : Type*} (T : WordChoiceTree α) : T.realChoice.height = T.height := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl => simp [realChoice, RealChoiceTree.height, WordChoiceTree.height, hu, hl]

theorem realChoice_mean {α : Type*} (T : WordChoiceTree α) (f : α → ℝ) : T.realChoice.mean f = T.decode.mean f := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    simp only [realChoice, RealChoiceTree.mean, decode, AdaptiveChoiceTree.mean, hu, hl, Rat.cast_div, Rat.cast_natCast]

theorem realChoice_forLeaves {α : Type*} (T : WordChoiceTree α) (P : α → Prop) :
    T.realChoice.ForLeaves P ↔ T.decode.ForLeaves P := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl => exact and_congr hu hl

end WordChoiceTree

namespace WordTransition

noncomputable def realTransition {S α : Type*} : WordTransition S α → RealTransition S α
  | .done x => .done x
  | .ask a b hb hab upper lower => .ask ((a : ℝ) / b)
      ⟨div_nonneg (Nat.cast_nonneg a) (by exact_mod_cast hb.le),
        (div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)⟩ upper lower

end WordTransition

namespace WordStateMachine

noncomputable def realMachine {S α : Type*} (m : WordStateMachine S α) : RealStateMachine S α where
  step := fun s => (m.step s).realTransition
  rank := m.rank
  progress := by
    intro s
    cases hs : m.step s with
    | done x => trivial
    | ask a b hb hab upper lower =>
      have h := m.progress s
      rw [hs] at h
      exact h

theorem realMachine_specification {S α : Type*} (m : WordStateMachine S α) (s : S) :
    (m.realMachine.specification s) = (m.specification s).realChoice := by
  have hAll : ∀ n, ∀ s, m.rank s = n → m.realMachine.specification s = (m.specification s).realChoice := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : m.step s with
      | done x =>
        have hReal : m.realMachine.step s = .done x := by simp only [realMachine, hs, WordTransition.realTransition]
        rw [RealStateMachine.specification_done _ _ _ hReal, m.specification_of_done s x hs]
        rfl
      | ask a b hb hab upper lower =>
        have hProgress := m.progress s
        rw [hs] at hProgress
        have hReal : m.realMachine.step s = (WordTransition.ask a b hb hab upper lower).realTransition := by
          simp only [realMachine, hs]
        conv_lhs => unfold RealStateMachine.specification
        rw [hReal]
        rw [m.specification_of_ask s a b hb hab upper lower hs]
        simp only [WordTransition.realTransition, WordChoiceTree.realChoice]
        rw [ih (m.rank upper) (by omega) upper rfl, ih (m.rank lower) (by omega) lower rfl]
  exact hAll (m.rank s) s rfl

end WordStateMachine
end Blotto
