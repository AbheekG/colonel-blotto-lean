import Blotto.GeneralPaperDyadicCompare

/-! Local error certificates for the actual stored positive arithmetic.
They include zero prefix mass and exact virtual halving. The selected global
precision turns these structural exponents into the paper's relative budget.
-/
namespace Blotto.GeneralPaperMassApproximation
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Bound (unit exponent : ℕ) (exact : ℚ) (stored : Number) : Prop :=
  Normal unit stored ∧ 0≤exact ∧ retention unit^exponent*exact≤value stored ∧ value stored≤exact

theorem zero_bound (unit exponent : ℕ) : Bound unit exponent 0 zero := by
  exact ⟨zero_normal unit,le_refl _,by simp [zero_value],by simp [zero_value]⟩

theorem weaken (unit small large : ℕ) (exact : ℚ) (stored : Number)
    (hUnit : 1<unit) (hOrder : small≤large) (h : Bound unit small exact stored) : Bound unit large exact stored := by
  have hr := retention_bounds unit hUnit
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr.1.le hr.2 hOrder) h.2.1
  exact ⟨h.1,h.2.1,he.trans h.2.2.1,h.2.2.2⟩

theorem half_bound (unit exponent : ℕ) (exact : ℚ) (stored : Number) (h : Bound unit exponent exact stored) :
    Bound unit exponent (exact/2) (GeneralPaperDyadicShift.shift stored (-1)) := by
  refine ⟨GeneralPaperDyadicShift.shift_normal unit stored (-1) h.1,div_nonneg h.2.1 (by norm_num),?_,?_⟩
  · rw [GeneralPaperDyadicShift.half_value]
    nlinarith only [h.2.2.1]
  · rw [GeneralPaperDyadicShift.half_value]
    exact div_le_div_of_nonneg_right h.2.2.2 (by norm_num)

theorem add_bound (unit p exponent : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (leftExact rightExact : ℚ) (left right : Number)
    (hl : Bound unit exponent leftExact left) (hr : Bound unit exponent rightExact right) :
    Bound unit (exponent+1) (leftExact+rightExact) (GeneralPaperDyadicAddition.add unit p left right).number := by
  have hRet := retention_bounds unit hUnit
  have ha := GeneralPaperDyadicAddition.add_certificate unit p hUnit hPower left right hl.1 hr.1
  have hLower := mul_le_mul_of_nonneg_left (add_le_add hl.2.2.1 hr.2.2.1) hRet.1.le
  have hEq : retention unit*(retention unit^exponent*leftExact+retention unit^exponent*rightExact)=
      retention unit^(exponent+1)*(leftExact+rightExact) := by rw [pow_succ]; ring
  rw [hEq] at hLower
  exact ⟨GeneralPaperDyadicAddition.add_normal unit p hUnit hPower left right hl.1 hr.1,
    add_nonneg hl.2.1 hr.2.1,hLower.trans ha.1,ha.2.trans (add_le_add hl.2.2.2 hr.2.2.2)⟩

def queryExponent (lambda k : ℕ) : ℕ :=
  (GeneralPaperPowerPrecision.levelBound lambda k+2)*(lambda+1)+GeneralPaperPowerPrecision.levelBound lambda k+1

def budget (lambda k : ℕ) : ℕ := queryExponent lambda k+lambda+2

theorem budget_factor (lambda k : ℕ) : budget lambda k≤GeneralPaperPowerPrecision.errorFactor lambda k := by
  unfold budget queryExponent GeneralPaperPowerPrecision.errorFactor
  nlinarith

theorem bernoulli (unit exponent : ℕ) (hUnit : 1<unit) :
    1-(exponent:ℚ)/unit≤retention unit^exponent := by
  have hr := retention_bounds unit hUnit
  have hr0 : (0:ℝ)≤retention unit := by exact_mod_cast hr.1.le
  have hr1 : (retention unit:ℝ)≤1 := by exact_mod_cast hr.2
  have he := GeneralPaperGeometricVariation.power_lower (retention unit:ℝ) hr0 hr1 exponent
  have hDef : 1-(retention unit:ℝ)=1/(unit:ℝ) := by simp [retention]
  rw [hDef] at he
  have hCast : ((1-(exponent:ℚ)/unit:ℚ):ℝ)≤((retention unit^exponent:ℚ):ℝ) := by
    push_cast
    convert he using 1 <;> ring
  exact_mod_cast hCast

theorem relative_bound (unit exponent : ℕ) (exact : ℚ) (stored : Number)
    (hUnit : 1<unit) (h : Bound unit exponent exact stored) :
    (1-(exponent:ℚ)/unit)*exact≤value stored ∧ value stored≤exact := by
  have he := mul_le_mul_of_nonneg_right (bernoulli unit exponent hUnit) h.2.1
  exact ⟨he.trans h.2.2.1,h.2.2.2⟩

theorem selected_relative (lambda k exponent : ℕ) (exact : ℚ) (stored : Number)
    (hExponent : exponent≤budget lambda k) (h : Bound (prepare lambda k).format.unit exponent exact stored) :
    (1-(GeneralPaperSourceParameters.prepare k).nu/64)*exact≤value stored ∧ value stored≤exact := by
  have he := relative_bound (prepare lambda k).format.unit exponent exact stored (GeneralPaperPowerPrecision.unit_positive lambda k) h
  have hUnit : (0:ℚ)<(prepare lambda k).format.unit := by exact_mod_cast GeneralPaperCachedMassJoin.prepared_unit_positive lambda k
  have hCap : (exponent:ℚ)≤GeneralPaperPowerPrecision.errorFactor lambda k := by
    exact_mod_cast hExponent.trans (budget_factor lambda k)
  have hPrecision := GeneralPaperPowerPrecision.precision_condition lambda k
  have hPrec : (GeneralPaperPowerPrecision.errorFactor lambda k:ℚ)/(prepare lambda k).format.unit≤
      (GeneralPaperSourceParameters.prepare k).nu/64 := by
    change (GeneralPaperPowerPrecision.errorFactor lambda k:ℚ)/(GeneralPaperPowerPrecision.prepare lambda k).unit≤_
    have hu : (0:ℚ)<(GeneralPaperPowerPrecision.prepare lambda k).unit := hUnit
    apply (div_le_iff₀ hu).mpr
    have hs := (div_le_iff₀ hu).mp hPrecision
    nlinarith only [hs]
  have hError := (div_le_div_of_nonneg_right hCap hUnit.le).trans hPrec
  have hScaled := mul_le_mul_of_nonneg_right (show 1-(GeneralPaperSourceParameters.prepare k).nu/64≤1-(exponent:ℚ)/(prepare lambda k).format.unit by linarith) h.2.1
  exact ⟨hScaled.trans he.1,he.2⟩

end Blotto.GeneralPaperMassApproximation
