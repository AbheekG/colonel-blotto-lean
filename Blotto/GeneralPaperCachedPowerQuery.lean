import Blotto.GeneralPaperPowerQueryArithmetic

/-! Queries consume the actual materialized table. The constructor supplies
every normality/degree/exponent premise; source level caps supply the query
range. No table, precision or power constructor is replayed by the query.
Both implementations preserve the whole native result and approximation.
-/
namespace Blotto.GeneralPaperCachedPowerQuery
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def query (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) :
    GeneralPaperRoundedPowerQuery.Result × ℕ :=
  GeneralPaperPowerQueryPrice.run primitive W c.powers.format.unit c.powers.format.fractionalBits c.powers.table exponent

def budget (prepared : GeneralPaperPreparedPowers.Prepared) : ℕ :=
  prepared.format.fractionalBits+prepared.format.columns*
    (GeneralPaperPowerTableBounds.budget prepared.format.fractionalBits prepared.format.columns prepared.base+
      prepared.format.fractionalBits+1)

def operandWidth (prepared : GeneralPaperPreparedPowers.Prepared) : ℕ :=
  GeneralPaperPowerQueryBounds.width prepared.format.fractionalBits prepared.format.columns (2^prepared.format.columns) (budget prepared)

def profile (primitive : ℕ → ℕ) (W : ℕ) (prepared : GeneralPaperPreparedPowers.Prepared) : ℕ :=
  2048*(prepared.format.columns+1)*(W+primitive (operandWidth prepared))

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ) :
    (query primitive W c exponent).1=GeneralPaperPreparedPowers.query c.powers exponent := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  have hu : 0<f.unit := Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hn := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k hu (GeneralPaperPowerPrecision.unit_power lambda k)
  have ht := GeneralPaperPowerQueryBounds.constructed f.unit f.fractionalBits f.columns
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) b.number hn.1 hn.2
  exact GeneralPaperPowerQueryPrice.data primitive W f.unit f.fractionalBits hu (GeneralPaperPowerPrecision.unit_power lambda k) _ ht.normal exponent

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (exponent : ℕ) (hExponent : exponent≤c.controls.precision.levelBound) :
    (query primitive W c exponent).2≤profile primitive W c.powers := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let table := (build f.unit f.fractionalBits b.number f.columns).entries
  let E := GeneralPaperPowerTableBounds.budget f.fractionalBits f.columns b.number
  let R := f.fractionalBits+f.columns*(E+f.fractionalBits+1)
  have hu : 0<f.unit := Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hn := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k hu (GeneralPaperPowerPrecision.unit_power lambda k)
  have ht := GeneralPaperPowerQueryBounds.constructed f.unit f.fractionalBits f.columns
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) b.number hn.1 hn.2
  have hLength : table.length=f.columns := entries_length f.unit f.fractionalBits f.columns b.number
  have hCap : exponent≤2^f.columns := by
    change exponent≤GeneralPaperPowerPrecision.levelBound lambda k at hExponent
    exact hExponent.trans (GeneralPaperPowerPrecision.width_cap lambda k).le
  have hBudget : f.fractionalBits+table.length*(E+f.fractionalBits+1)≤R := by rw [hLength]
  have h := GeneralPaperPowerQueryPrice.work primitive hMono W f.unit f.fractionalBits f.columns (2^f.columns) E R hu
    (GeneralPaperPowerPrecision.unit_power lambda k) table ht hLength.le exponent hCap hBudget
  rw [hLength] at h
  exact h

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) : GeneralPaperRoundedPowerQuery.Result × ℕ :=
  GeneralPaperPowerQueryArithmetic.run c.powers.format.unit c.powers.format.fractionalBits c.powers.table exponent

theorem arithmetic_data (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) :
    (arithmetic c exponent).1=GeneralPaperPreparedPowers.query c.powers exponent :=
  GeneralPaperPowerQueryArithmetic.data _ _ _ _

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ) :
    (arithmetic c exponent).2≤262144*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have h := GeneralPaperPowerQueryArithmetic.work f.unit f.fractionalBits
    (GeneralPaperPreparedPowers.prepare lambda k).table exponent
  have hLength : (GeneralPaperPreparedPowers.prepare lambda k).table.length=f.columns := entries_length _ _ _ _
  rw [hLength] at h
  have hProfile : f.columns*(12*(f.fractionalBits+1)+194)+80≤GeneralPaperCachedPowerPreparation.arithmeticProfile lambda k := by
    unfold GeneralPaperCachedPowerPreparation.arithmeticProfile
    change _≤512*(f.fractionalBits+2)+f.columns*(12*(f.fractionalBits+1)+194)+144
    omega
  exact h.trans (hProfile.trans (GeneralPaperPowerPreparationEnvelope.arithmetic_profile m lambda k Qv))

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ) :
    (query primitive W c exponent).1=(arithmetic c exponent).1 := by rw [data _ _ _ _ _ _ _ hc,arithmetic_data]

theorem approximation (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (hExponent : exponent≤c.controls.precision.levelBound) :
    (query primitive W c exponent).1.remaining=0 ∧
      Normal c.controls.precision.parameters.unit (query primitive W c exponent).1.number ∧
      0<(query primitive W c exponent).1.number.mantissa ∧
      |(GeneralPaperGeometricLevels.geometricBase c.controls.source.eta c.controls.source.theta:ℝ)^exponent-
        (value (query primitive W c exponent).1.number:ℝ)|≤(c.controls.source.nu:ℝ)/1024 := by
  rw [data primitive W m lambda k Qv c hc]
  subst c
  have hc := GeneralPaperPreparedPowers.query_certificate lambda k exponent hExponent
  exact ⟨hc.1,hc.2.1,hc.2.2.1,GeneralPaperPreparedPowers.query_error lambda k exponent hExponent⟩

end Blotto.GeneralPaperCachedPowerQuery
