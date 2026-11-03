import Blotto.GeneralPaperEpochCachedQuery

/-! For a fixed stored prefix and total, increasing the target can only
change a left decision to a right decision. This is exact scaled integer
comparison, independent of the numerical mass-error analysis.
-/
namespace Blotto.GeneralPaperQuantileOrderCompare
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperQuantileComparison
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem scaled_bound (lambda k factor : ℕ) (x : Number)
    (hFactor : factor≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hNormal : Normal (prepare lambda k).format.unit x) :
    (GeneralPaperDyadicCompare.scale factor x).mantissa<2^width lambda k := by
  have hu : (prepare lambda k).format.unit=2^(prepare lambda k).format.fractionalBits :=
    GeneralPaperPowerPrecision.unit_power lambda k
  have hm := normal_mantissa_bits _ x (hu ▸ hNormal)
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  exact GeneralPaperDyadicCompare.scale_bound _ (34+k) factor x hm (by simpa only [hs] using hFactor)

theorem choose_exact (lambda k j : ℕ) (total prefixMass : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hTotal : Normal (prepare lambda k).format.unit total)
    (hPrefix : Normal (prepare lambda k).format.unit prefixMass) :
    (choose lambda k j total prefixMass).answer=true ↔
      (j:ℚ)*value total≤((GeneralPaperSourceParameters.prepare k).summarySize:ℚ)*value prefixMass :=
  GeneralPaperDyadicCompare.scaled_correct _ _ _ _ _
    (scaled_bound lambda k j total hJ hTotal) (scaled_bound lambda k _ prefixMass (le_refl _) hPrefix)

theorem choose_antitone (lambda k small large : ℕ) (total prefixMass : Number)
    (hOrder : small≤large) (hLarge : large≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hTotal : Normal (prepare lambda k).format.unit total)
    (hPrefix : Normal (prepare lambda k).format.unit prefixMass) :
    (choose lambda k large total prefixMass).answer=true →
      (choose lambda k small total prefixMass).answer=true := by
  intro hChoose
  have hl := (choose_exact lambda k large total prefixMass hLarge hTotal hPrefix).mp hChoose
  apply (choose_exact lambda k small total prefixMass (hOrder.trans hLarge) hTotal hPrefix).mpr
  have hj : (small:ℚ)≤large := by exact_mod_cast hOrder
  exact (mul_le_mul_of_nonneg_right hj (value_nonnegative total)).trans hl

end Blotto.GeneralPaperQuantileOrderCompare
