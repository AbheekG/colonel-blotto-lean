import Blotto.GeneralPaperEpochPowerQueries

/-! Bounded normalization of an integer mantissa at an explicitly supplied
dyadic scale. The quotient depth depends on the mantissa precision, never on
the magnitude of an encoded exponent.
-/
namespace Blotto.GeneralPaperMantissaQuotient
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem spec (unit p input scale : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hScale : 0<scale) (hLow : unit*scale≤ input) (hHigh : input<2*unit*scale) :
    (input:ℚ)=(scale:ℚ)*(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient+
      (GeneralPaperBoundedQuotient.run input scale (p+1)).remainder ∧
    0≤(GeneralPaperBoundedQuotient.run input scale (p+1)).remainder ∧
      (GeneralPaperBoundedQuotient.run input scale (p+1)).remainder<scale := by
  have hs : (0:ℚ)<scale := by exact_mod_cast hScale
  apply GeneralPaperBoundedQuotient.run_spec _ _ hs (p+1) (by positivity)
  have he : (input:ℚ)<2*(unit:ℚ)*(scale:ℚ) := by exact_mod_cast hHigh
  have hp : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  rw [hp] at he
  rw [pow_succ]
  nlinarith only [he]

theorem normal (unit p input scale : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hScale : 0<scale) (hLow : unit*scale≤ input) (hHigh : input<2*unit*scale) :
    unit≤(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient ∧
      (GeneralPaperBoundedQuotient.run input scale (p+1)).quotient<2*unit := by
  have hs := spec unit p input scale hUnit hPower hScale hLow hHigh
  have hd : (0:ℚ)<scale := by exact_mod_cast hScale
  have hlo : (unit:ℚ)*(scale:ℚ)≤ input := by exact_mod_cast hLow
  have hhi : (input:ℚ)<2*(unit:ℚ)*(scale:ℚ) := by exact_mod_cast hHigh
  constructor
  · by_contra hn
    have hq : ((GeneralPaperBoundedQuotient.run input scale (p+1)).quotient:ℚ)+1≤unit :=
      by exact_mod_cast (show (GeneralPaperBoundedQuotient.run input scale (p+1)).quotient+1≤unit by omega)
    nlinarith only [hs.1,hs.2.2,hd,hlo,hq]
  · by_contra hn
    have hq : 2*(unit:ℚ)≤(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient :=
      by exact_mod_cast (show 2*unit≤(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient by omega)
    nlinarith only [hs.1,hs.2.1,hd,hhi,hq]

theorem relative (unit p input scale : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hScale : 0<scale) (hLow : unit*scale≤ input) (hHigh : input<2*unit*scale) :
    retention unit*(input:ℚ)≤(scale:ℚ)*(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient ∧
      (scale:ℚ)*(GeneralPaperBoundedQuotient.run input scale (p+1)).quotient≤ input := by
  have hs := spec unit p input scale hUnit hPower hScale hLow hHigh
  have hu : (0:ℚ)<unit := by exact_mod_cast hUnit
  have hl : (unit:ℚ)*(scale:ℚ)≤ input := by exact_mod_cast hLow
  refine ⟨?_,by linarith only [hs.1,hs.2.1]⟩
  unfold retention
  apply (mul_le_mul_iff_right₀ hu).mp
  have hi : (1/(unit:ℚ))*(unit:ℚ)=1 := one_div_mul_cancel (ne_of_gt hu)
  nlinarith only [hs.1,hs.2.2,hl,hi]

end Blotto.GeneralPaperMantissaQuotient
