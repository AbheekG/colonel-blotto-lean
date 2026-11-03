import Blotto.GeneralPaperScaledComparisonPrice
import Blotto.GeneralPaperActualFreshMassPrice

/-! The quantile comparator consumes the width and summary size retained
by preparation. Normality, exponent range and the summary index discharge
all bit operand bounds. No parameter constructor is executed by this call.
-/
namespace Blotto.GeneralPaperQuantileComparisonPrice
open GeneralPaperDyadicFloat GeneralPaperDyadicCompare
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W digits : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (j : ℕ) (total storedPrefix : Number) : GeneralPaperDyadicCompare.Result × ℕ :=
  GeneralPaperScaledComparisonPrice.run primitive W digits j total c.controls.source.summarySize storedPrefix

def arithmetic (digits : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (j : ℕ) (total storedPrefix : Number) : GeneralPaperDyadicCompare.Result × ℕ :=
  GeneralPaperScaledComparisonPrice.arithmetic digits j total c.controls.source.summarySize storedPrefix

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv digits : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (j : ℕ) (total storedPrefix : Number) :
    (run primitive W digits c j total storedPrefix).1=GeneralPaperQuantileComparison.choose lambda k j total storedPrefix := by
  unfold run
  rw [GeneralPaperScaledComparisonPrice.data,hc,hDigits]
  rfl

theorem arithmetic_data (m lambda k Qv digits : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (j : ℕ) (total storedPrefix : Number) :
    (arithmetic digits c j total storedPrefix).1=GeneralPaperQuantileComparison.choose lambda k j total storedPrefix := by
  unfold arithmetic
  rw [GeneralPaperScaledComparisonPrice.arithmetic_data,hc,hDigits]
  rfl

theorem inputs (lambda k j : ℕ) (total storedPrefix : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hTotal : Normal (GeneralPaperPowerPrecision.prepare lambda k).unit total)
    (hPrefix : Normal (GeneralPaperPowerPrecision.prepare lambda k).unit storedPrefix) :
    let d := GeneralPaperQuantileComparison.width lambda k
    j<2^d ∧ (GeneralPaperSourceParameters.prepare k).summarySize<2^d ∧
      total.mantissa<2^d ∧ storedPrefix.mantissa<2^d ∧
      (scale j total).mantissa<2^d ∧
      (scale (GeneralPaperSourceParameters.prepare k).summarySize storedPrefix).mantissa<2^d := by
  let p := (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
  let d := GeneralPaperQuantileComparison.width lambda k
  have hPower := GeneralPaperPowerPrecision.unit_power lambda k
  have ht := normal_mantissa_bits p total (hPower ▸ hTotal)
  have hp := normal_mantissa_bits p storedPrefix (hPower ▸ hPrefix)
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  have hScale : (GeneralPaperSourceParameters.prepare k).summarySize<2^d := by
    rw [hs]
    apply Nat.pow_lt_pow_right (by decide : 1<2)
    dsimp [d,GeneralPaperQuantileComparison.width,GeneralPaperPreparedPowers.prepare]
    omega
  have hMono : 2^(p+1)≤2^d := by
    apply Nat.pow_le_pow_right (by decide : 0<2)
    dsimp [d,p,GeneralPaperQuantileComparison.width,GeneralPaperPreparedPowers.prepare]
    omega
  have hLeft := scale_bound p (34+k) j total ht (by simpa only [hs] using hJ)
  have hRight := scale_bound p (34+k) (GeneralPaperSourceParameters.prepare k).summarySize storedPrefix hp (by rw [hs])
  exact ⟨hJ.trans_lt hScale,hScale,ht.trans_le hMono,hp.trans_le hMono,hLeft,hRight⟩

theorem digits_bound (m lambda k Qv : ℕ) :
    GeneralPaperQuantileComparison.width lambda k+1≤256*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+1+(34+k)+1≤_
  omega

theorem operand_width (m lambda k Qv : ℕ) (total storedPrefix : Number)
    (hTotal : total.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k)
    (hPrefix : storedPrefix.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    GeneralPaperDyadicComparisonEnvelope.width (GeneralPaperQuantileComparison.width lambda k) total storedPrefix≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hL := (binaryWordWidth_mono hTotal).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hR := (binaryWordWidth_mono hPrefix).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hD := digits_bound m lambda k Qv
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperDyadicComparisonEnvelope.width GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (j : ℕ) (total storedPrefix : Number)
    (hJ : j≤c.controls.source.summarySize) (hTotal : Normal c.powers.format.unit total)
    (hPrefix : Normal c.powers.format.unit storedPrefix)
    (hTotalCap : total.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k)
    (hPrefixCap : storedPrefix.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    (run primitive W digits c j total storedPrefix).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  subst c
  subst digits
  have hi := inputs lambda k j total storedPrefix hJ hTotal hPrefix
  have h := GeneralPaperScaledComparisonPrice.work primitive hMono W (GeneralPaperQuantileComparison.width lambda k)
    j total (GeneralPaperSourceParameters.prepare k).summarySize storedPrefix
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
  exact h.trans (Nat.mul_le_mul
    (by have hd:=digits_bound m lambda k Qv; nlinarith only [hd])
    (Nat.add_le_add_left (hMono (operand_width m lambda k Qv total storedPrefix hTotalCap hPrefixCap)) W))

theorem arithmetic_work (m lambda k Qv digits : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (j : ℕ) (total storedPrefix : Number) :
    (arithmetic digits c j total storedPrefix).2≤262144*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
  have h := GeneralPaperScaledComparisonPrice.arithmetic_work digits j total c.controls.source.summarySize storedPrefix
  rw [hDigits] at h
  have hd := digits_bound m lambda k Qv
  unfold arithmetic
  rw [hDigits]
  nlinarith only [h,hd]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv digits : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (j : ℕ) (total storedPrefix : Number) :
    (run primitive W digits c j total storedPrefix).1=(arithmetic digits c j total storedPrefix).1 := by
  rw [data primitive W m lambda k Qv digits c hc hDigits,arithmetic_data m lambda k Qv digits c hc hDigits]

end Blotto.GeneralPaperQuantileComparisonPrice
