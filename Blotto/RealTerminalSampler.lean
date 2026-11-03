import Blotto.RealTerminalPivot
import Blotto.RealTerminalGroups

/-! An explicit pivot scan selects the uniform or mixed terminal program.
The returned native array has the retained whole-allocation law and budgets. -/

namespace Blotto.TerminalLotto
open MeasureTheory
open scoped Classical

noncomputable def realSampleArray {n : ℕ} (i : TerminalLotto n) (seed : RealFourSeed) : FixedArrayTable n ℝ :=
  match hp : i.realPivot with
  | none => i.realUniformArray (i.realPivot_none.mp hp) seed
  | some pivot => i.realMixedArray pivot (i.realPivot_some hp) seed

noncomputable def realSample {n : ℕ} (i : TerminalLotto n) (seed : RealFourSeed) : Allocation n :=
  (i.realSampleArray seed).read

theorem realSample_eq_uniform {n : ℕ} (i : TerminalLotto n) (h : ∀ j, ¬Fractional i.length i.resource j) :
    i.realSample = i.realUniformSample h := by
  funext seed
  unfold realSample realSampleArray
  split
  · rfl
  · rename_i pivot hp
    exact False.elim (h pivot (i.realPivot_some hp))

theorem realSample_eq_mixed {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : i.realSample = i.realMixedSample pivot hp := by
  funext seed
  unfold realSample realSampleArray
  split
  · rename_i hn
    exact False.elim ((i.realPivot_none.mp hn) pivot hp)
  · rename_i j hj
    have he := i.fractional_unique (i.realPivot_some hj) hp
    cases he
    rfl

theorem realSample_measurable {n : ℕ} (i : TerminalLotto n) : Measurable i.realSample := by
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · have hp := (mem_fractionalSet _ _ _).mp h.choose_spec
    rw [i.realSample_eq_mixed h.choose hp]
    exact i.realMixedSample_measurable h.choose hp
  · have hn : ∀ j, ¬Fractional i.length i.resource j := fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩
    rw [i.realSample_eq_uniform hn]
    exact i.realUniformSample_measurable hn

theorem realSample_law {n : ℕ} (i : TerminalLotto n) :
    Measure.map i.realSample (FourInput.realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation n)) := by
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · have hp := (mem_fractionalSet _ _ _).mp h.choose_spec
    rw [law, dite_eq_left h, i.realSample_eq_mixed h.choose hp]
    exact i.realMixedSample_law h.choose hp
  · have hn : ∀ j, ¬Fractional i.length i.resource j := fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩
    rw [law, dite_eq_right h, i.realSample_eq_uniform hn]
    exact i.realUniformSample_law hn

theorem realSample_fullBudget {n : ℕ} (i : TerminalLotto n) (seed : RealFourSeed) (hs : realGroupSeedValid seed) :
    FullBudget i.B (i.realSample seed) := by
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · have hp := (mem_fractionalSet _ _ _).mp h.choose_spec
    rw [i.realSample_eq_mixed h.choose hp]
    exact i.realMixedSample_fullBudget h.choose hp seed hs
  · have hn : ∀ j, ¬Fractional i.length i.resource j := fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩
    rw [i.realSample_eq_uniform hn]
    exact i.realUniformSample_fullBudget hn seed hs

theorem realSampleArray_fullBudget {n : ℕ} (i : TerminalLotto n) (seed : RealFourSeed) (hs : realGroupSeedValid seed) :
    FullBudget i.B (i.realSampleArray seed).read := i.realSample_fullBudget seed hs

end Blotto.TerminalLotto
