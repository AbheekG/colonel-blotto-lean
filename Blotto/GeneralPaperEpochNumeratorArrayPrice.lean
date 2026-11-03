import Blotto.GeneralPaperLocalNumeratorPrice
import Blotto.GeneralPaperPowerQueryEnvelope
import Blotto.GeneralPaperSummaryArrayControls
import Blotto.GeneralPaperControlArrayPrice
import Blotto.GeneralPaperEpochPowerQueries

/-! One retained-table power query and integer conversion per occurrence.
The same indexed fill retains repeated occurrence slots in both models.
-/
namespace Blotto.GeneralPaperEpochNumeratorArrayPrice
open GeneralPaperDyadicFloat
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {n : ℕ} (bits : Bool) (price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (levels : FixedArrayTable n ℕ) (r : Fin n) : ℕ × ℕ :=
  let power := if bits then GeneralPaperCachedPowerQuery.query price W c (levels.read r)
    else GeneralPaperCachedPowerQuery.arithmetic c (levels.read r)
  let converted := GeneralPaperLocalNumeratorPrice.run (if bits then price else fun _ => 1) W
    c.powers.format.unit c.powers.format.fractionalBits power.1.number
  (converted.1,power.2+converted.2+32*W)

def run {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (levels : FixedArrayTable n ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W) (element bits price W c levels)

theorem element_data {n : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (r : Fin n) :
    (element bits price W c levels r).1=GeneralPaperLocalPowerNumerators.numerator
      c.powers.format.unit c.powers.format.fractionalBits (GeneralPaperPreparedPowers.query c.powers (levels.read r)).number := by
  cases bits <;> simp only [element,Bool.false_eq_true,ite_false,ite_true,GeneralPaperLocalNumeratorPrice.data,
    GeneralPaperCachedPowerQuery.arithmetic_data,GeneralPaperCachedPowerQuery.data price W m lambda k Qv c hc]

theorem data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) :
    (run bits index price W c levels).1=GeneralPaperEpochPowerQueries.buildNumerators c.powers levels := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  unfold GeneralPaperEpochPowerQueries.buildNumerators
  congr 1
  funext r
  exact element_data bits price W m lambda k Qv c hc levels r

def elementProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  131072*GeneralPaperSourcePreparationSizes.measure m lambda k Qv*
    (W+price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))+
    6*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*W

def arithmeticElementProfile (m lambda k Qv : ℕ) : ℕ :=
  262144*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2+102

def profile (price : ℕ → ℕ) (W m lambda k Qv n : ℕ) : ℕ :=
  n*elementProfile price W m lambda k Qv+44*(n+1)*arrayWord W n

def arithmeticProfile (m lambda k Qv n : ℕ) : ℕ := n*arithmeticElementProfile m lambda k Qv+44*(n+1)

theorem element_bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (r : Fin n) (hLevel : levels.read r≤c.controls.precision.levelBound) :
    (element true price W c levels r).2≤elementProfile price W m lambda k Qv := by
  let power := GeneralPaperCachedPowerQuery.query price W c (levels.read r)
  have hd := GeneralPaperCachedPowerQuery.data price W m lambda k Qv c hc (levels.read r)
  have hDegree : levels.read r≤GeneralPaperPowerPrecision.levelBound lambda k := by
    have h := hLevel
    rw [hc] at h
    exact h
  have hn : Normal c.powers.format.unit power.1.number := by
    change Normal c.powers.format.unit (GeneralPaperCachedPowerQuery.query price W c (levels.read r)).1.number
    rw [hd,hc]
    exact (GeneralPaperPreparedPowers.query_certificate lambda k _ hDegree).2.1
  have he := GeneralPaperPowerQueryExponent.cached price W m lambda k Qv c hc _ hLevel
  have hCap : power.1.number.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
    change power.1.number.exponent.natAbs≤c.controls.precision.levelBound+c.powers.format.fractionalBits at he
    apply he.trans
    rw [hc]
    unfold GeneralPaperQuantileExponentRange.cap
    change GeneralPaperPowerPrecision.levelBound lambda k+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits≤_
    omega
  have hw : GeneralPaperLocalNumeratorPrice.width c.powers.format.unit c.powers.format.fractionalBits power.1.number≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hc]
    exact GeneralPaperLocalNumeratorPrice.operand_width m lambda k Qv power.1.number hCap
  have hConvert := (GeneralPaperLocalNumeratorPrice.work price hMono W c.powers.format.unit c.powers.format.fractionalBits
    power.1.number hn).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (hMono hw)) _)
  have hQuery := GeneralPaperPowerQueryEnvelope.work price hMono W m lambda k Qv c hc _ hLevel
  change power.2≤_ at hQuery
  change power.2+(GeneralPaperLocalNumeratorPrice.run price W c.powers.format.unit c.powers.format.fractionalBits power.1.number).2+32*W≤_
  unfold elementProfile
  omega

theorem element_arithmetic_work {n : ℕ} (price : ℕ → ℕ) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (r : Fin n) (hLevel : levels.read r≤c.controls.precision.levelBound) :
    (element false price 1 c levels r).2≤arithmeticElementProfile m lambda k Qv := by
  have hDegree : levels.read r≤GeneralPaperPowerPrecision.levelBound lambda k := by
    have h := hLevel
    rw [hc] at h
    exact h
  have hn : Normal c.powers.format.unit (GeneralPaperCachedPowerQuery.arithmetic c (levels.read r)).1.number := by
    rw [GeneralPaperCachedPowerQuery.arithmetic_data,hc]
    exact (GeneralPaperPreparedPowers.query_certificate lambda k _ hDegree).2.1
  have hcvt := GeneralPaperLocalNumeratorPrice.arithmetic_work c.powers.format.unit c.powers.format.fractionalBits _ hn
  have hq := GeneralPaperCachedPowerQuery.arithmetic_work m lambda k Qv c hc (levels.read r)
  change (GeneralPaperCachedPowerQuery.arithmetic c (levels.read r)).2+
    (GeneralPaperLocalNumeratorPrice.run (fun _ => 1) 1 c.powers.format.unit c.powers.format.fractionalBits
      (GeneralPaperCachedPowerQuery.arithmetic c (levels.read r)).1.number).2+32≤_
  unfold arithmeticElementProfile
  omega

theorem bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    (run true (fun w => w) price W c levels).2≤profile price W m lambda k Qv n :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) _ (element true price W c levels)
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n)
    (fun r => element_bit_work price hMono W m lambda k Qv c hc levels r (hLevels r))

theorem arithmetic_work {n : ℕ} (price : ℕ → ℕ) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    (run false (fun _ => 1) price 1 c levels).2≤arithmeticProfile m lambda k Qv n := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _ (element false price 1 c levels)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun r => element_arithmetic_work price m lambda k Qv c hc levels r (hLevels r))
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile] using h

theorem returned_bound {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) (r : Fin n) :
    (run bits index price W c levels).1.read r≤4*c.powers.format.unit := by
  rw [data bits index price W m lambda k Qv c hc,GeneralPaperEpochPowerQueries.read_numerators]
  apply GeneralPaperLocalNumeratorPrice.bound
  rw [hc]
  have hDegree : levels.read r≤GeneralPaperPowerPrecision.levelBound lambda k := by
    have h := hLevels r
    rw [hc] at h
    exact h
  exact (GeneralPaperPreparedPowers.query_certificate lambda k _ hDegree).2.1

theorem same_data {n : ℕ} (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : FixedArrayTable n ℕ) :
    (run true (fun w => w) price W c levels).1=(run false (fun _ => 1) price 1 c levels).1 := by
  rw [data true (fun w => w) price W m lambda k Qv c hc,data false (fun _ => 1) price 1 m lambda k Qv c hc]

end Blotto.GeneralPaperEpochNumeratorArrayPrice
