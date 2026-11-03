import Blotto.PRGAccuracyLogarithm

/-! Exact agreement with the appendix's K=ceil(log_2(32/epsilon)).
Only the proof uses real logarithms; the executed selector remains the
existing integer/Boolean ratio algorithm, including nonreduced raw words.
-/

namespace Blotto.BinaryAccuracyInput

theorem precision_eq_paper_ceil (a : BinaryAccuracyInput) :
    a.precision=⌈Real.logb 2 (32/a.real)⌉₊ := by
  let scaled : BinaryAccuracyInput :=
    ⟨a.numerator,32*a.denominator,a.numerator_pos,Nat.mul_pos (by decide) a.denominator_pos⟩
  have hReal : 1/scaled.real=32/a.real := by
    have hn : (a.numerator:ℝ)≠0 := by exact_mod_cast ne_of_gt a.numerator_pos
    have hd : (a.denominator:ℝ)≠0 := by exact_mod_cast ne_of_gt a.denominator_pos
    dsimp [scaled,real]
    push_cast
    field_simp [hn,hd]
  have h := scaled.logExponent_eq_ceil
  change a.precision=⌈Real.logb 2 (1/scaled.real)⌉₊ at h
  rw [hReal] at h
  exact h

end Blotto.BinaryAccuracyInput

namespace Blotto

theorem rationalAccuracyPrecision_eq_paper_ceil (ε : ℚ) (hε : 0<ε) :
    rationalAccuracyPrecision ε=⌈Real.logb 2 (32/(ε:ℝ))⌉₊ := by
  have h := (BinaryAccuracyInput.ofPositiveRational ε hε).precision_eq_paper_ceil
  simpa only [BinaryAccuracyInput.ofPositiveRational_precision,BinaryAccuracyInput.ofPositiveRational_real] using h

end Blotto

namespace Blotto.BinaryAccuracyWords

theorem precision_eq_paper_ceil (a : BinaryAccuracyWords) :
    a.precision=⌈Real.logb 2 (32/a.numeric.real)⌉₊ := by
  rw [a.precision_eq]
  exact a.numeric.precision_eq_paper_ceil

end Blotto.BinaryAccuracyWords
