import Blotto.RationalCategorical

/-! The categorical controller's ideal law has the exact normalized weighted
expectation. Zero residual mass is treated explicitly, so unused zero-weight
tails do not introduce a positivity assumption or a partial operation. -/

namespace Blotto

namespace RationalWeightList

theorem weightedSum_zero {α : Type*} (l : RationalWeightList α) (f : α → ℝ)
    (hm : l.mass = 0) : l.weightedSum f = 0 := by
  cases l with
  | mk items hn =>
    change (items.map (fun item => (item.2 : ℝ) * f item.1)).sum = 0
    change (items.map Prod.snd).sum = 0 at hm
    induction items with
    | nil => rfl
    | cons head rest ih =>
      have hhead : 0 ≤ head.2 := hn head (by simp)
      have hrest : ∀ item ∈ rest, 0 ≤ item.2 := fun item hi => hn item (by simp [hi])
      have hsum : 0 ≤ (rest.map Prod.snd).sum := (RationalWeightList.mk rest hrest).mass_nonnegative
      have hh : head.2 = 0 := by simp only [List.map_cons, List.sum_cons] at hm; linarith
      have ht : (rest.map Prod.snd).sum = 0 := by simp only [List.map_cons, List.sum_cons] at hm; linarith
      simp only [List.map_cons, List.sum_cons, hh, Rat.cast_zero, zero_mul, zero_add]
      exact ih hrest ht

def first {α : Type*} (l : RationalWeightList α) (fallback : α) : α :=
  ((l.items.head?).map Prod.fst).getD fallback

noncomputable def average {α : Type*} (l : RationalWeightList α) (fallback : α) (f : α → ℝ) : ℝ :=
  if 0 < l.mass then l.weightedSum f / (l.mass : ℝ) else f (l.first fallback)

end RationalWeightList

noncomputable def categoricalValue {α : Type*} (fallback : α) (f : α → ℝ) : CategoricalState α → ℝ
  | .selected x => f x
  | .remaining l => l.average fallback f

theorem categoricalTransition_value {α : Type*} (fallback : α) (f : α → ℝ)
    (cursor : CategoricalState α) :
    match categoricalTransition fallback cursor with
    | .done x => f x = categoricalValue fallback f cursor
    | .ask a b _ _ upper lower => categoricalValue fallback f cursor =
        ((a : ℚ) / b : ℝ) * categoricalValue fallback f upper +
          (1 - ((a : ℚ) / b : ℝ)) * categoricalValue fallback f lower := by
  cases cursor with
  | selected x => rfl
  | remaining l =>
    cases l with
    | mk items hn =>
      cases items with
      | nil => simp [categoricalTransition, categoricalValue, RationalWeightList.average,
          RationalWeightList.mass, RationalWeightList.first]
      | cons head rest =>
        cases rest with
        | nil =>
          dsimp [categoricalTransition, categoricalValue, RationalWeightList.average,
            RationalWeightList.mass, RationalWeightList.weightedSum, RationalWeightList.first]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_cases hm : 0 < head.2
          · rw [ite_eq_left hm]
            have hreal : (head.2 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
            field_simp
          · rw [ite_eq_right hm]
        | cons next tail =>
          let l : RationalWeightList α := ⟨head :: next :: tail, hn⟩
          let t : RationalWeightList α := ⟨next :: tail, fun item hi => hn item (by simp [hi])⟩
          unfold categoricalTransition
          dsimp only
          by_cases hm : 0 < l.mass
          · rw [dite_eq_left hm]
            have hh : 0 ≤ head.2 := hn head (by simp)
            have hle : head.2 ≤ l.mass := by
              change head.2 ≤ head.2 + t.mass
              linarith [t.mass_nonnegative]
            let hp : 0 ≤ head.2 / l.mass ∧ head.2 / l.mass ≤ 1 :=
              ⟨div_nonneg hh (le_of_lt hm), (div_le_one hm).mpr hle⟩
            have hc := congrArg (fun q : ℚ => (q : ℝ)) (ProbabilityWords.ofRat_rational (head.2 / l.mass) hp)
            simp only [ProbabilityWords.rational, Rat.cast_div, Rat.cast_natCast] at hc
            change l.average fallback f =
              (((ProbabilityWords.ofRat (head.2 / l.mass) hp).numerator : ℝ) /
                (ProbabilityWords.ofRat (head.2 / l.mass) hp).denominator) * f head.1 +
                (1 - (((ProbabilityWords.ofRat (head.2 / l.mass) hp).numerator : ℝ) /
                (ProbabilityWords.ofRat (head.2 / l.mass) hp).denominator)) * t.average fallback f
            rw [hc]
            have hl : (l.mass : ℝ) = (head.2 : ℝ) + (t.mass : ℝ) := by
              simp [l, t, RationalWeightList.mass]
            have hs : l.weightedSum f = (head.2 : ℝ) * f head.1 + t.weightedSum f := rfl
            have hnz : (l.mass : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
            unfold RationalWeightList.average
            rw [ite_eq_left hm, hs]
            by_cases ht : 0 < t.mass
            · rw [ite_eq_left ht]
              have htnz : (t.mass : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
              field_simp
              rw [hl]
              ring
            · rw [ite_eq_right ht]
              have ht0 : t.mass = 0 := le_antisymm (le_of_not_gt ht) t.mass_nonnegative
              rw [t.weightedSum_zero f ht0]
              have hh0 : (head.2 : ℝ) = (l.mass : ℝ) := by simpa [ht0] using hl.symm
              rw [hh0]
              simp [hnz]
          · rw [dite_eq_right hm]
            change f head.1 = l.average fallback f
            simp [RationalWeightList.average, hm, RationalWeightList.first, l]

theorem categoricalMachine_mean {α : Type*} (fallback : α) (f : α → ℝ)
    (l : RationalWeightList α) (hm : 0 < l.mass) :
    ((categoricalMachine fallback).specification (.remaining l)).decode.mean f =
      l.weightedSum f / (l.mass : ℝ) := by
  have h := (categoricalMachine fallback).specification_mean (categoricalValue fallback f) f
    (by
      intro s
      have hv := categoricalTransition_value fallback f s
      unfold categoricalMachine
      dsimp only
      cases hs : categoricalTransition fallback s with
      | done x => rw [hs] at hv; exact hv
      | ask a b hb hab upper lower =>
        rw [hs] at hv
        simpa only [Rat.cast_div, Rat.cast_natCast] using hv) (.remaining l)
  simpa only [categoricalValue, RationalWeightList.average, ite_eq_left hm] using h

end Blotto
