import Blotto.GeneralPaperRoundedAdditionEnvelope

/-! Rounded addition on the retained source format. Reached normality and
the paper exponent range derive the operand word; no parameter builder or
encoding oracle is executed by an addition call.
-/
namespace Blotto.GeneralPaperQuantileAdditionPrice
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (left right : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  GeneralPaperRoundedAdditionExecution.run primitive W c.powers.format.unit c.powers.format.fractionalBits left right

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) (left right : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  GeneralPaperRoundedAdditionExecution.arithmetic c.powers.format.unit c.powers.format.fractionalBits left right

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (left right : Number)
    (hLeft : Normal c.powers.format.unit left) (hRight : Normal c.powers.format.unit right) :
    (run primitive W c left right).1=GeneralPaperDyadicAddition.add c.powers.format.unit c.powers.format.fractionalBits left right := by
  apply GeneralPaperRoundedAdditionExecution.data primitive W _ _ _ _ left right hLeft hRight
  · rw [hc]; exact Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  · rw [hc]; exact GeneralPaperPowerPrecision.unit_power lambda k

theorem arithmetic_data (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (left right : Number)
    (hLeft : Normal c.powers.format.unit left) (hRight : Normal c.powers.format.unit right) :
    (arithmetic c left right).1=GeneralPaperDyadicAddition.add c.powers.format.unit c.powers.format.fractionalBits left right := by
  apply GeneralPaperRoundedAdditionExecution.arithmetic_data _ _ _ _ left right hLeft hRight
  · rw [hc]; exact Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  · rw [hc]; exact GeneralPaperPowerPrecision.unit_power lambda k

theorem precision_bound (m lambda k Qv : ℕ) :
    (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+1≤128*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
  have h := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  omega

theorem operand_width (m lambda k Qv : ℕ) (left right : Number)
    (hLeft : left.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k)
    (hRight : right.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    GeneralPaperRoundedAdditionOperands.width (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits left right≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hl := (binaryWordWidth_mono hLeft).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hr := (binaryWordWidth_mono hRight).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperRoundedAdditionOperands.width GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (left right : Number) (hLeft : Normal c.powers.format.unit left) (hRight : Normal c.powers.format.unit right)
    (hLeftCap : left.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k)
    (hRightCap : right.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    (run primitive W c left right).2≤524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hu : 0<c.powers.format.unit := by rw [hc]; exact Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hp : c.powers.format.unit=2^c.powers.format.fractionalBits := by rw [hc]; exact GeneralPaperPowerPrecision.unit_power lambda k
  have h := GeneralPaperRoundedAdditionEnvelope.work primitive hMono W _ _ hu hp left right hLeft hRight
  have hw : GeneralPaperRoundedAdditionOperands.width c.powers.format.fractionalBits left right≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hc]; exact operand_width m lambda k Qv left right hLeftCap hRightCap
  have hd : c.powers.format.fractionalBits+1≤128*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
    rw [hc]; exact precision_bound m lambda k Qv
  exact h.trans (Nat.mul_le_mul (by nlinarith only [hd]) (Nat.add_le_add_left (hMono hw) W))

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (left right : Number) :
    (arithmetic c left right).2≤262144*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
  have h := GeneralPaperRoundedAdditionArithmetic.work c.powers.format.unit c.powers.format.fractionalBits left right
  have hd : c.powers.format.fractionalBits+1≤128*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1) := by
    rw [hc]; exact precision_bound m lambda k Qv
  change (GeneralPaperRoundedAdditionExecution.arithmetic _ _ _ _).2≤_
  nlinarith only [h,hd]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (left right : Number)
    (hLeft : Normal c.powers.format.unit left) (hRight : Normal c.powers.format.unit right) :
    (run primitive W c left right).1=(arithmetic c left right).1 := by
  rw [data primitive W m lambda k Qv c hc left right hLeft hRight,
    arithmetic_data m lambda k Qv c hc left right hLeft hRight]

end Blotto.GeneralPaperQuantileAdditionPrice
