import Blotto.RealCategoricalMachine
import Blotto.RealStateMachineMean

/-! Exact normalized categorical means include zero remaining mass. Cached
mass is a semantic equality, not a supplied probability approximation. -/

namespace Blotto
open scoped Classical

namespace RealWeightList

def weightedSum {α : Type*} (l : RealWeightList α) (f : α → ℝ) : ℝ :=
  (l.items.map (fun item => item.2 * f item.1)).sum

def first {α : Type*} (l : RealWeightList α) (fallback : α) : α :=
  ((l.items.head?).map Prod.fst).getD fallback

noncomputable def average {α : Type*} (l : RealWeightList α) (fallback : α) (f : α → ℝ) : ℝ :=
  if 0 < l.mass then l.weightedSum f / l.mass else f (l.first fallback)

theorem weightedSum_zero {α : Type*} (l : RealWeightList α) (f : α → ℝ) (hm : l.mass = 0) : l.weightedSum f = 0 := by
  have hZero : (l.items.map Prod.snd).sum = 0 := l.mass_eq.symm.trans hm
  unfold weightedSum
  have hAll : ∀ items : List (α × ℝ), (∀ item ∈ items, 0 ≤ item.2) → (items.map Prod.snd).sum = 0 →
      (items.map (fun item => item.2 * f item.1)).sum = 0 := by
    intro items
    induction items with
    | nil => intros; rfl
    | cons head rest ih =>
      intro hn hs
      have hh : 0 ≤ head.2 := hn head (by simp)
      have ht : ∀ item ∈ rest, 0 ≤ item.2 := fun item hi => hn item (by simp [hi])
      have hSum : 0 ≤ (rest.map Prod.snd).sum := by
        apply List.sum_nonneg
        intro q hq
        rcases List.mem_map.mp hq with ⟨item, hi, rfl⟩
        exact ht item hi
      have hh0 : head.2 = 0 := by simp only [List.map_cons, List.sum_cons] at hs; linarith
      have ht0 : (rest.map Prod.snd).sum = 0 := by simp only [List.map_cons, List.sum_cons] at hs; linarith
      simpa [hh0] using ih ht ht0
  exact hAll l.items l.nonnegative hZero

end RealWeightList

noncomputable def realCategoricalValue {α : Type*} (fallback : α) (f : α → ℝ) : RealCategoricalState α → ℝ
  | .selected x => f x
  | .remaining l => l.average fallback f

theorem realCategoricalStep_value {α : Type*} (fallback : α) (f : α → ℝ) (cursor : RealCategoricalState α) :
    match realCategoricalStep fallback cursor with
    | .done x => f x = realCategoricalValue fallback f cursor
    | .ask p _ upper lower => realCategoricalValue fallback f cursor =
        p * realCategoricalValue fallback f upper + (1 - p) * realCategoricalValue fallback f lower := by
  rw [realCategoricalStep_refines]
  cases cursor with
  | selected x => rfl
  | remaining l =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil =>
        have hm : mass = 0 := by simpa using hEq
        simp [realCategoricalStepReference, realCategoricalValue, RealWeightList.average, RealWeightList.first, hm]
      | cons head rest =>
        cases rest with
        | nil =>
          have hm : mass = head.2 := by simpa using hEq
          simp only [realCategoricalStepReference]
          simp only [realCategoricalValue, RealWeightList.average, RealWeightList.weightedSum,
            RealWeightList.first, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            List.head?_cons, Option.map_some, Option.getD_some]
          change f head.1 = if 0 < mass then (head.2 * f head.1) / mass else f head.1
          by_cases hPos : 0 < mass
          · rw [ite_eq_left hPos, ← hm]
            field_simp
          · rw [ite_eq_right hPos]
        | cons next tail =>
          let l : RealWeightList α := ⟨head :: next :: tail, mass, hEq, hn⟩
          let t := l.tail head (next :: tail) rfl
          have hMass : l.mass = head.2 + t.mass := by dsimp [t, RealWeightList.tail]; ring
          have hSum : l.weightedSum f = head.2 * f head.1 + t.weightedSum f := by
            simp [RealWeightList.weightedSum, l, t, RealWeightList.tail]
          unfold realCategoricalStepReference
          dsimp only
          by_cases hPos : 0 < mass
          · rw [dite_eq_left hPos]
            change l.average fallback f = head.2 / l.mass * f head.1 + (1 - head.2 / l.mass) * t.average fallback f
            unfold RealWeightList.average
            rw [ite_eq_left hPos, hSum]
            have hLne : l.mass ≠ 0 := ne_of_gt (show 0 < l.mass from hPos)
            by_cases ht : 0 < t.mass
            · rw [ite_eq_left ht]
              field_simp [hLne, ne_of_gt ht]
              rw [hMass]
              ring
            · rw [ite_eq_right ht]
              have ht0 : t.mass = 0 := le_antisymm (le_of_not_gt ht) t.mass_nonnegative
              rw [t.weightedSum_zero f ht0]
              have hh : head.2 = l.mass := by linarith [hMass]
              rw [hh]
              simp [hLne]
          · rw [dite_eq_right hPos]
            simp [realCategoricalValue, RealWeightList.average, hPos, RealWeightList.first]

theorem realCategoricalMachine_mean {α : Type*} (fallback : α) (f : α → ℝ) (l : RealWeightList α) (hm : 0 < l.mass) :
    ((realCategoricalMachine fallback).specification (.remaining l)).mean f = l.weightedSum f / l.mass := by
  have h := (realCategoricalMachine fallback).specification_mean (realCategoricalValue fallback f) f
    (by
      intro s
      have hv := realCategoricalStep_value fallback f s
      unfold realCategoricalMachine
      dsimp only
      cases hs : realCategoricalStep fallback s with
      | done x => rw [hs] at hv; exact hv
      | ask p hp upper lower => rw [hs] at hv; exact hv) (.remaining l)
  simpa only [realCategoricalValue, RealWeightList.average, ite_eq_left hm] using h

end Blotto
