import Blotto.GeneralPaperRankedInterval

/-! Two unrounded CDF errors and one separate mesh rounding give the
interval error 10*nu+theta. No mesh error is charged at either endpoint.
-/
namespace Blotto.GeneralPaperIntervalError
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem from_prefix_errors {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1))
    (hOrder : lo≤hi) (hTotal : 0<∑ r, values.read r) (trueLo trueHi error : ℝ)
    (hLo : |trueLo-((GeneralPaperEpochPrefixArray.build values).read lo:ℝ)/
      ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)|≤error)
    (hHi : |trueHi-((GeneralPaperEpochPrefixArray.build values).read hi:ℝ)/
      ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)|≤error) :
    |(trueHi-trueLo)-(GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (GeneralPaperIntervalQuery.evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient:ℝ)|≤
      2*error+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hl := abs_le.mp hLo
  have hh := abs_le.mp hHi
  have hRaw : |(trueHi-trueLo)-(GeneralPaperPrefixInterval.numerator (GeneralPaperEpochPrefixArray.build values) lo hi:ℝ)/
      ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)|≤2*error := by
    rw [GeneralPaperPrefixInterval.ratio_real values lo hi hOrder]
    apply abs_le.mpr
    constructor <;> linarith
  exact GeneralPaperCDFMesh.selected_true_error k _ _
    (by rw [GeneralPaperEpochPrefixQuery.read_total]; exact hTotal)
    (GeneralPaperPrefixInterval.numerator_le_total values lo hi) _ _ hRaw

end Blotto.GeneralPaperIntervalError
