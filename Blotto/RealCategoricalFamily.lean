import Blotto.RealCategoricalReference

/-! Joint measurability of the actual cached-mass controller for measurable
real weight families. The head/tail expression is only a proof reference. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

theorem realCategoricalReference_measurable {θ α : Type*} [MeasurableSpace θ] [MeasurableSpace α]
    (fallback : α) (C : ℕ) (indices : List α) (weight : θ → α → ℝ)
    (mass : θ → ℝ) (seed : θ → Fin C → ℝ)
    (hw : ∀ j, Measurable (fun z => weight z j)) (hm : Measurable mass) (hs : Measurable seed) :
    Measurable (fun z => realCategoricalReference fallback C
      (indices.map fun j => (j, weight z j)) (mass z) (seed z)) := by
  induction C generalizing indices mass with
  | zero =>
    cases indices with
    | nil => exact measurable_const
    | cons head rest =>
      cases rest with
      | nil => exact measurable_const
      | cons next tail =>
        change Measurable (fun z => if 0 < mass z then fallback else head)
        exact Measurable.ite (measurableSet_lt measurable_const hm) measurable_const measurable_const
  | succ C ih =>
    cases indices with
    | nil => exact measurable_const
    | cons head rest =>
      cases rest with
      | nil => exact measurable_const
      | cons next tail =>
        have hTail : Measurable (fun z => Fin.tail (seed z)) := by
          apply Measurable.of_eval
          intro j
          exact (measurable_pi_apply j.succ).comp hs
        have hRest := ih (next :: tail) (fun z => mass z - weight z head)
          (fun z => Fin.tail (seed z)) (hm.sub (hw head)) hTail
        change Measurable (fun z => if 0 < mass z then
          if seed z 0 ≤ weight z head / mass z then head else
            realCategoricalReference fallback C
              ((next :: tail).map fun j => (j, weight z j)) (mass z - weight z head) (Fin.tail (seed z))
          else head)
        exact Measurable.ite (measurableSet_lt measurable_const hm)
          (Measurable.ite (measurableSet_le ((measurable_pi_apply 0).comp hs) ((hw head).div hm))
            measurable_const hRest) measurable_const

theorem realCategorical_measurable_family {θ : Type*} [MeasurableSpace θ] {k : ℕ}
    (weight : θ → Fin k → ℝ) (h : ∀ z j, 0 ≤ weight z j) (fallback : Fin k)
    (seed : θ → Fin (k - 1) → ℝ) (hw : ∀ j, Measurable (fun z => weight z j)) (hs : Measurable seed) :
    Measurable (fun z => realCategorical (weight z) (h z) fallback (seed z)) := by
  have hEq : (fun z => realCategorical (weight z) (h z) fallback (seed z)) =
      (fun z => realCategoricalReference fallback (k - 1)
        ((List.ofFn id : List (Fin k)).map fun j => (j, weight z j)) (∑ j, weight z j) (seed z)) := by
    funext z
    rw [realCategorical_eq_reference]
    simp [List.map_ofFn]
  rw [hEq]
  exact realCategoricalReference_measurable fallback (k - 1) _ weight _ seed hw
    (Finset.measurable_sum _ fun j _ => hw j) hs

theorem realCategorical_measurable_joint {θ : Type*} [MeasurableSpace θ] {k : ℕ}
    (weight : θ → Fin k → ℝ) (h : ∀ z j, 0 ≤ weight z j) (fallback : Fin k)
    (hw : ∀ j, Measurable (fun z => weight z j)) :
    Measurable (fun z : θ × (Fin (k - 1) → ℝ) => realCategorical (weight z.1) (h z.1) fallback z.2) := by
  exact realCategorical_measurable_family (θ := θ × (Fin (k - 1) → ℝ))
    (fun z => weight z.1) (fun z => h z.1) fallback (fun z => z.2)
    (fun j => (hw j).comp measurable_fst) measurable_snd

end Blotto
