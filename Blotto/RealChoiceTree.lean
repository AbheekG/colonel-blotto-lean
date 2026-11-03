import Blotto.RealUniformInputs

/-! Exact real-choice semantics driven by fresh continuous unit inputs.
This finite tree is a specification; a state implementation must refine it
without constructing all unvisited branches. -/

namespace Blotto
open MeasureTheory
open scoped Classical

inductive RealChoiceTree (α : Type*) where
  | leaf (value : α)
  | fork (p : ℝ) (normalized : 0 ≤ p ∧ p ≤ 1) (upper lower : RealChoiceTree α)

namespace RealChoiceTree

def height {α : Type*} : RealChoiceTree α → ℕ
  | .leaf _ => 0
  | .fork _ _ upper lower => 1 + max upper.height lower.height

def ForLeaves {α : Type*} (P : α → Prop) : RealChoiceTree α → Prop
  | .leaf x => P x
  | .fork _ _ upper lower => upper.ForLeaves P ∧ lower.ForLeaves P

noncomputable def sample {α : Type*} : (C : ℕ) → RealChoiceTree α → (Fin C → ℝ) → Option α × ℕ
  | 0, T, _ => match T with
    | .leaf x => (some x, 0)
    | .fork _ _ _ _ => (none, 0)
  | C + 1, T, seed => match T with
    | .leaf x => (some x, 0)
    | .fork p _ upper lower =>
      let result := (if seed 0 ≤ p then upper else lower).sample C (Fin.tail seed)
      (result.1, result.2 + 1)

noncomputable def output {α : Type*} (T : RealChoiceTree α) (C : ℕ) (fallback : α) (seed : Fin C → ℝ) : α :=
  (T.sample C seed).1.getD fallback

theorem sample_fork_succ {α : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : RealChoiceTree α)
    (C : ℕ) (seed : Fin (C + 1) → ℝ) :
    (fork p hp upper lower).sample (C + 1) seed =
      (let result := (if seed 0 ≤ p then upper else lower).sample C (Fin.tail seed)
       (result.1, result.2 + 1)) := rfl

theorem sample_reads_le {α : Type*} (T : RealChoiceTree α) (C : ℕ) (seed : Fin C → ℝ) :
    (T.sample C seed).2 ≤ C := by
  induction C generalizing T with
  | zero => cases T <;> rfl
  | succ C ih =>
    cases T with
    | leaf x => simp [sample]
    | fork p hp upper lower =>
      rw [sample_fork_succ]
      dsimp only
      split
      · exact Nat.add_le_add_right (ih upper (Fin.tail seed)) 1
      · exact Nat.add_le_add_right (ih lower (Fin.tail seed)) 1

theorem sample_reads_height {α : Type*} (T : RealChoiceTree α) (C : ℕ) (seed : Fin C → ℝ) :
    (T.sample C seed).2 ≤ T.height := by
  induction C generalizing T with
  | zero => cases T <;> simp [sample, height]
  | succ C ih =>
    cases T with
    | leaf x => rfl
    | fork p hp upper lower =>
      rw [sample_fork_succ]
      dsimp only
      split
      · have h := ih upper (Fin.tail seed)
        change _ ≤ 1 + max upper.height lower.height
        omega
      · have h := ih lower (Fin.tail seed)
        change _ ≤ 1 + max upper.height lower.height
        omega

theorem sample_total {α : Type*} (T : RealChoiceTree α) (C : ℕ) (seed : Fin C → ℝ) (h : T.height ≤ C) :
    (T.sample C seed).1 ≠ none := by
  induction C generalizing T with
  | zero =>
    cases T with
    | leaf x => simp [sample]
    | fork p hp upper lower => simp [height] at h
  | succ C ih =>
    cases T with
    | leaf x => simp [sample]
    | fork p hp upper lower =>
      have hUpper : upper.height ≤ C := by simp only [height] at h; omega
      have hLower : lower.height ≤ C := by simp only [height] at h; omega
      rw [sample_fork_succ]
      dsimp only
      split
      · exact ih upper (Fin.tail seed) hUpper
      · exact ih lower (Fin.tail seed) hLower

theorem sample_forLeaves {α : Type*} (T : RealChoiceTree α) (P : α → Prop) (hT : T.ForLeaves P)
    (C : ℕ) (seed : Fin C → ℝ) {x : α} (h : (T.sample C seed).1 = some x) : P x := by
  induction C generalizing T with
  | zero =>
    cases T with
    | leaf y => cases Option.some.inj h; exact hT
    | fork p hp upper lower => cases h
  | succ C ih =>
    cases T with
    | leaf y => cases Option.some.inj h; exact hT
    | fork p hp upper lower =>
      rw [sample_fork_succ] at h
      dsimp only at h
      split at h
      · exact ih upper hT.1 (Fin.tail seed) h
      · exact ih lower hT.2 (Fin.tail seed) h

theorem output_forLeaves {α : Type*} (T : RealChoiceTree α) (P : α → Prop) (hT : T.ForLeaves P)
    (C : ℕ) (fallback : α) (hFallback : P fallback) (seed : Fin C → ℝ) : P (T.output C fallback seed) := by
  unfold output
  cases h : (T.sample C seed).1 with
  | none => exact hFallback
  | some x => exact T.sample_forLeaves P hT C seed h

theorem output_fork_succ {α : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : RealChoiceTree α)
    (C : ℕ) (fallback : α) (seed : Fin (C + 1) → ℝ) :
    (fork p hp upper lower).output (C + 1) fallback seed =
      RealThresholdChoice.sample p (upper.output C fallback (Fin.tail seed)) (lower.output C fallback (Fin.tail seed)) (seed 0) := by
  unfold output RealThresholdChoice.sample
  rw [sample_fork_succ]
  dsimp only
  split <;> rfl

noncomputable def idealLaw {α : Type*} [MeasurableSpace α] : RealChoiceTree α → ProbabilityMeasure α
  | .leaf x => RealThresholdChoice.pointLaw x
  | .fork p hp upper lower =>
    probabilityMixture ![p, 1 - p] ![upper.idealLaw, lower.idealLaw]
      (by intro j; fin_cases j; exact hp.1; exact sub_nonneg.mpr hp.2) (by simp)

theorem measurable_output {α : Type*} [MeasurableSpace α] (T : RealChoiceTree α) (C : ℕ) (fallback : α) :
    Measurable (T.output C fallback) := by
  induction C generalizing T with
  | zero => cases T <;> exact measurable_const
  | succ C ih =>
    cases T with
    | leaf x => exact measurable_const
    | fork p hp upper lower =>
      have hUpper := ih upper
      have hLower := ih lower
      have hm := RealIndependentChoice.measurable_sample p _ _ hUpper hLower
      have he : (fork p hp upper lower).output (C + 1) fallback =
          RealIndependentChoice.sample p (upper.output C fallback) (lower.output C fallback) ∘ RealUniformInputs.split := by
        funext seed
        exact output_fork_succ p hp upper lower C fallback seed
      rw [he]
      exact hm.comp (RealUniformInputs.measurable_split C)

end RealChoiceTree
end Blotto
