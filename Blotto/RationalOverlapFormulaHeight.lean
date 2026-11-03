import Blotto.RationalOverlapCompiler
import Blotto.OverlapFormulaBounds
import Blotto.RationalOverlapHeight

/-! The counted evaluator's complete operands have fixed-depth height bounds.
Exact descriptor refinement separately preserves the sharper old output bound. -/

namespace Blotto.RationalOverlapFormula
open OverlapFormulaCode

theorem environment_height {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    ∀ r, RationalHeight ((environment G B i j).read r) s := by
  intro r
  fin_cases r
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 0).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 1).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 2).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 0).2
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 1).2
  · simpa [environment, FixedArrayTable.read_ofFn] using (hFirst.2 i 2).2
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 0).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 1).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 2).1
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 0).2
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 1).2
  · simpa [environment, FixedArrayTable.read_ofFn] using (hSecond.2 j 2).2
  · simpa [environment, FixedArrayTable.read_ofFn] using hFirst.1 i
  · simpa [environment, FixedArrayTable.read_ofFn] using hSecond.1 j
  · simpa [environment, FixedArrayTable.read_ofFn] using hD
  · simpa [environment, FixedArrayTable.read_ofFn] using hB

theorem descriptor_height {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    (descriptor G B).HeightAt (expressionHeightBudget s 6) := by
  rw [descriptor_eq]
  exact G.descriptor_height B s hs hFirst hSecond hD hB

theorem weight_intermediates {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    weight.AllRunHeights (environment G B i j) (expressionHeightBudget s 7) :=
  OverlapFormulaCode.weight_intermediates _ s hs (environment_height G B i j s hFirst hSecond hD hB)

theorem safeP_intermediates {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    (safeP r).AllRunHeights (environment G B i j) (expressionHeightBudget s 9) :=
  OverlapFormulaCode.safeP_intermediates r _ s hs (environment_height G B i j s hFirst hSecond hD hB)

theorem safeQ_intermediates {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    (safeQ r).AllRunHeights (environment G B i j) (expressionHeightBudget s 9) :=
  OverlapFormulaCode.safeQ_intermediates r _ s hs (environment_height G B i j s hFirst hSecond hD hB)

theorem weight_wordWidth {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    rationalWordWidth (weight.value (environment G B i j)) ≤ 256 * s + 255 := by
  have hh := (weight.run_height _ s (environment_height G B i j s hFirst hSecond hD hB)
    (weight.LiteralHeights_mono hs weight_literals)).mono (expressionHeightBudget_mono s weight_depth)
  have hw := rationalWordWidth_of_height hh
  change rationalWordWidth (weight.value (environment G B i j)) ≤ 1 + 2 * expressionHeightBudget s 7 at hw
  norm_num [expressionHeightBudget] at hw
  omega

theorem safeP_wordWidth {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    rationalWordWidth ((safeP r).value (environment G B i j)) ≤ 1024 * s + 1023 := by
  have hh := ((safeP r).run_height _ s (environment_height G B i j s hFirst hSecond hD hB)
    ((safeP r).LiteralHeights_mono hs (safeP_literals r))).mono (expressionHeightBudget_mono s (safeP_depth r))
  have hw := rationalWordWidth_of_height hh
  change rationalWordWidth ((safeP r).value (environment G B i j)) ≤ 1 + 2 * expressionHeightBudget s 9 at hw
  norm_num [expressionHeightBudget] at hw
  omega

theorem safeQ_wordWidth {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    rationalWordWidth ((safeQ r).value (environment G B i j)) ≤ 1024 * s + 1023 := by
  have hh := ((safeQ r).run_height _ s (environment_height G B i j s hFirst hSecond hD hB)
    ((safeQ r).LiteralHeights_mono hs (safeQ_literals r))).mono (expressionHeightBudget_mono s (safeQ_depth r))
  have hw := rationalWordWidth_of_height hh
  change rationalWordWidth ((safeQ r).value (environment G B i j)) ≤ 1 + 2 * expressionHeightBudget s 9 at hw
  norm_num [expressionHeightBudget] at hw
  omega

end Blotto.RationalOverlapFormula
