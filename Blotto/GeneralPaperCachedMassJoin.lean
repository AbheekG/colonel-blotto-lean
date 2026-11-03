import Blotto.GeneralPaperDyadicShift

/-! Actual fresh parent-cache recomputation from two child caches and their
integer offsets. The old parent mass is not an input. The error exponent
depends on current child height and the global offset cap, not on how many
times a parent was recomputed. Sparse range-update/tree-shape invariants and
the quantile traversal are separate obligations.
-/
namespace Blotto.GeneralPaperCachedMassJoin
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperGeometricLevels
open GeneralPaperDyadicMultiply (Result)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (k : ℕ) : ℚ := geometricBase (GeneralPaperSourceParameters.prepare k).eta
  (GeneralPaperSourceParameters.prepare k).theta

def applyOffset (prepared : Prepared) (offset : ℕ) (mass : Number) : Result :=
  let power := query prepared offset
  let product := GeneralPaperDyadicMultiply.multiply prepared.format.unit prepared.format.fractionalBits power.number mass
  ⟨product.number,power.work+product.work+16⟩

def recompute (prepared : Prepared) (leftOffset : ℕ) (leftMass : Number)
    (rightOffset : ℕ) (rightMass : Number) : Result :=
  let left := applyOffset prepared leftOffset leftMass
  let right := applyOffset prepared rightOffset rightMass
  let sum := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits left.number right.number
  ⟨sum.number,left.work+right.work+sum.work+24⟩

theorem prepared_unit_positive (lambda k : ℕ) : 0<(prepare lambda k).format.unit :=
  Nat.zero_lt_one.trans (GeneralPaperPowerPrecision.unit_positive lambda k)

theorem base_positive (k : ℕ) : 0<base k := by
  have hp := GeneralPaperSourceParameters.positive k
  have he := base_bounds _ _ hp.2.1 hp.2.2.2 (GeneralPaperSourceParameters.eta_theta k)
  unfold base
  linarith [he.1]

theorem apply_normal (lambda k offset : ℕ) (mass : Number)
    (hOffset : offset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hNormal : Normal (prepare lambda k).format.unit mass) :
    Normal (prepare lambda k).format.unit (applyOffset (prepare lambda k) offset mass).number := by
  have hp := query_certificate lambda k offset hOffset
  exact GeneralPaperDyadicMultiply.multiply_normal _ _
    (prepared_unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hp.2.1 hNormal

theorem apply_positive (lambda k offset : ℕ) (mass : Number)
    (hOffset : offset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hNormal : Normal (prepare lambda k).format.unit mass) (hPositive : 0<mass.mantissa) :
    0<(applyOffset (prepare lambda k) offset mass).number.mantissa := by
  have hp := query_certificate lambda k offset hOffset
  exact GeneralPaperDyadicMultiply.multiply_positive _ _
    (prepared_unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hp.2.1 hNormal hp.2.2.1 hPositive

theorem apply_bounds (lambda k offset errorDepth : ℕ) (mass : Number) (exactMass : ℚ)
    (hOffset : offset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hNormal : Normal (prepare lambda k).format.unit mass) (hExact : 0≤exactMass)
    (hLower : retention (prepare lambda k).format.unit^errorDepth*exactMass≤value mass)
    (hUpper : value mass≤exactMass) :
    retention (prepare lambda k).format.unit^(errorDepth+GeneralPaperPowerPrecision.levelBound lambda k+1)*
        (base k^offset*exactMass)≤value (applyOffset (prepare lambda k) offset mass).number ∧
      value (applyOffset (prepare lambda k) offset mass).number≤base k^offset*exactMass := by
  let r := retention (prepare lambda k).format.unit
  have hr := retention_bounds (prepare lambda k).format.unit (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hp := query_certificate lambda k offset hOffset
  have hPowerLower : r^offset*base k^offset≤value (query (prepare lambda k) offset).number := hp.2.2.2.1
  have hPowerUpper : value (query (prepare lambda k) offset).number≤base k^offset := hp.2.2.2.2
  have hMon : r^GeneralPaperPowerPrecision.levelBound lambda k≤r^offset := pow_le_pow_of_le_one hr.1.le hr.2 hOffset
  have hScaled := mul_le_mul_of_nonneg_right hMon (pow_nonneg (base_positive k).le offset)
  have hPow := hScaled.trans hPowerLower
  have hProduct := mul_le_mul hPow hLower
    (mul_nonneg (pow_nonneg hr.1.le errorDepth) hExact) (value_nonnegative _)
  have hRetained := mul_le_mul_of_nonneg_left hProduct hr.1.le
  have hm := GeneralPaperDyadicMultiply.multiply_certificate (prepare lambda k).format.unit
    (prepare lambda k).format.fractionalBits (prepared_unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ mass hp.2.1 hNormal
  have hLowerEq : r*((r^GeneralPaperPowerPrecision.levelBound lambda k*base k^offset)*
      (r^errorDepth*exactMass))=r^(errorDepth+GeneralPaperPowerPrecision.levelBound lambda k+1)*(base k^offset*exactMass) := by
    simp only [pow_add,pow_one]
    ring
  rw [hLowerEq] at hRetained
  have hProductUpper := mul_le_mul hPowerUpper hUpper (value_nonnegative mass)
    (pow_nonneg (base_positive k).le offset)
  exact ⟨hRetained.trans hm.1,hm.2.trans hProductUpper⟩

theorem recompute_normal (lambda k leftOffset rightOffset : ℕ) (leftMass rightMass : Number)
    (hlOffset : leftOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hrOffset : rightOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hlNormal : Normal (prepare lambda k).format.unit leftMass)
    (hrNormal : Normal (prepare lambda k).format.unit rightMass) :
    Normal (prepare lambda k).format.unit (recompute (prepare lambda k) leftOffset leftMass rightOffset rightMass).number :=
  GeneralPaperDyadicAddition.add_normal _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ _
    (apply_normal lambda k leftOffset leftMass hlOffset hlNormal) (apply_normal lambda k rightOffset rightMass hrOffset hrNormal)

theorem recompute_positive (lambda k leftOffset rightOffset : ℕ) (leftMass rightMass : Number)
    (hlOffset : leftOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hrOffset : rightOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hlNormal : Normal (prepare lambda k).format.unit leftMass)
    (hrNormal : Normal (prepare lambda k).format.unit rightMass) (hlPositive : 0<leftMass.mantissa) :
    0<(recompute (prepare lambda k) leftOffset leftMass rightOffset rightMass).number.mantissa :=
  GeneralPaperDyadicAddition.add_positive _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ _
    (apply_normal lambda k leftOffset leftMass hlOffset hlNormal) (apply_normal lambda k rightOffset rightMass hrOffset hrNormal)
    (Or.inl (apply_positive lambda k leftOffset leftMass hlOffset hlNormal hlPositive))

theorem recompute_bounds (lambda k height leftOffset rightOffset : ℕ) (leftMass rightMass : Number)
    (leftExact rightExact : ℚ)
    (hlOffset : leftOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hrOffset : rightOffset≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hlNormal : Normal (prepare lambda k).format.unit leftMass)
    (hrNormal : Normal (prepare lambda k).format.unit rightMass)
    (hlExact : 0≤leftExact) (hrExact : 0≤rightExact)
    (hlLower : retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height)*leftExact≤value leftMass)
    (hrLower : retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height)*rightExact≤value rightMass)
    (hlUpper : value leftMass≤leftExact) (hrUpper : value rightMass≤rightExact) :
    retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*(height+1))*
        (base k^leftOffset*leftExact+base k^rightOffset*rightExact)≤
          value (recompute (prepare lambda k) leftOffset leftMass rightOffset rightMass).number ∧
      value (recompute (prepare lambda k) leftOffset leftMass rightOffset rightMass).number≤
        base k^leftOffset*leftExact+base k^rightOffset*rightExact := by
  let r := retention (prepare lambda k).format.unit
  let C := (GeneralPaperPowerPrecision.levelBound lambda k+2)*height
  have hr := retention_bounds (prepare lambda k).format.unit (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hl := apply_bounds lambda k leftOffset C leftMass leftExact hlOffset hlNormal hlExact hlLower hlUpper
  have hh := apply_bounds lambda k rightOffset C rightMass rightExact hrOffset hrNormal hrExact hrLower hrUpper
  have hAdd := GeneralPaperDyadicAddition.add_certificate (prepare lambda k).format.unit
    (prepare lambda k).format.fractionalBits (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) _ _
    (apply_normal lambda k leftOffset leftMass hlOffset hlNormal) (apply_normal lambda k rightOffset rightMass hrOffset hrNormal)
  have hSum := mul_le_mul_of_nonneg_left (add_le_add hl.1 hh.1) hr.1.le
  have hExp : C+GeneralPaperPowerPrecision.levelBound lambda k+1+1=
      (GeneralPaperPowerPrecision.levelBound lambda k+2)*(height+1) := by dsimp [C]; ring
  have hEq : r*(r^(C+GeneralPaperPowerPrecision.levelBound lambda k+1)*(base k^leftOffset*leftExact)+
      r^(C+GeneralPaperPowerPrecision.levelBound lambda k+1)*(base k^rightOffset*rightExact))=
      r^((GeneralPaperPowerPrecision.levelBound lambda k+2)*(height+1))*
        (base k^leftOffset*leftExact+base k^rightOffset*rightExact) := by
    rw [← mul_add,← mul_assoc,mul_comm r,← pow_succ,hExp]
  rw [hEq] at hSum
  exact ⟨hSum.trans hAdd.1,hAdd.2.trans (add_le_add hl.2 hh.2)⟩

theorem apply_work (prepared : Prepared) (offset : ℕ) (mass : Number) : (applyOffset prepared offset mass).work≤
    (query prepared offset).work+12*(prepared.format.fractionalBits+1)+82 := by
  have he := GeneralPaperDyadicMultiply.multiply_work prepared.format.unit prepared.format.fractionalBits (query prepared offset).number mass
  change (query prepared offset).work+(GeneralPaperDyadicMultiply.multiply _ _ _ _).work+16≤_
  omega

theorem recompute_work (prepared : Prepared) (leftOffset rightOffset : ℕ) (leftMass rightMass : Number) :
    (recompute prepared leftOffset leftMass rightOffset rightMass).work≤
      (query prepared leftOffset).work+(query prepared rightOffset).work+
        8*prepared.format.fractionalBits+36*(prepared.format.fractionalBits+1)+272 := by
  have hl := apply_work prepared leftOffset leftMass
  have hr := apply_work prepared rightOffset rightMass
  have ha := GeneralPaperDyadicAddition.add_work prepared.format.unit prepared.format.fractionalBits
    (applyOffset prepared leftOffset leftMass).number (applyOffset prepared rightOffset rightMass).number
  change (applyOffset prepared leftOffset leftMass).work+(applyOffset prepared rightOffset rightMass).work+
    (GeneralPaperDyadicAddition.add _ _ _ _).work+24≤_
  omega

end Blotto.GeneralPaperCachedMassJoin
