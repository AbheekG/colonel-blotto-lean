import Blotto.GeneralPaperStoredGeometricBase

/-! One actual shared power preparation, then queries on its stored table.
The precision constructor, exact dyadic base, rounded mantissa multiplication,
table builder and evaluator are joined here. Reference rational/real powers
occur only in proofs. Full primitive bit/storage prices remain separate.
-/
namespace Blotto.GeneralPaperPreparedPowers
open scoped BigOperators Classical
open GeneralPaperDyadicFloat GeneralPaperGeometricLevels
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared where
  format : GeneralPaperPowerPrecision.Parameters
  base : Number
  table : List GeneralPaperRoundedPowerTable.Entry
  work : ℕ

def prepare (lambda k : ℕ) : Prepared :=
  let format := GeneralPaperPowerPrecision.prepare lambda k
  let base := GeneralPaperStoredGeometricBase.construct format.unit format.fractionalBits k
  let table := GeneralPaperRoundedPowerTable.build format.unit format.fractionalBits base.number format.columns
  ⟨format,base.number,table.entries,format.work+base.work+table.work+24⟩

def query (prepared : Prepared) (exponent : ℕ) : GeneralPaperRoundedPowerQuery.Result :=
  GeneralPaperRoundedPowerQuery.evaluate prepared.format.unit prepared.format.fractionalBits prepared.table exponent

theorem prepared_base (lambda k : ℕ) :
    Normal (prepare lambda k).format.unit (prepare lambda k).base ∧
      0<(prepare lambda k).base.mantissa ∧ value (prepare lambda k).base=
        geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta := by
  have he := GeneralPaperStoredGeometricBase.construct_normal _ _ k
    (show 0<(GeneralPaperPowerPrecision.prepare lambda k).unit by have := GeneralPaperPowerPrecision.unit_positive lambda k; omega)
    (GeneralPaperPowerPrecision.unit_power lambda k)
  exact ⟨he.1,he.2,GeneralPaperStoredGeometricBase.selected_value lambda k⟩

theorem query_certificate (lambda k exponent : ℕ) (hExponent : exponent≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (query (prepare lambda k) exponent).remaining=0 ∧
    Normal (prepare lambda k).format.unit (query (prepare lambda k) exponent).number ∧
    0<(query (prepare lambda k) exponent).number.mantissa ∧
    retention (prepare lambda k).format.unit^exponent*
      (geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta)^exponent≤
      value (query (prepare lambda k) exponent).number ∧
    value (query (prepare lambda k) exponent).number≤
      (geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta)^exponent := by
  have hb := prepared_base lambda k
  have hc := GeneralPaperPowerPrecision.width_cap lambda k
  have he := GeneralPaperRoundedPowerQuery.evaluate_constructed _ _
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k)
    (prepare lambda k).base hb.1 hb.2.1 (prepare lambda k).format.columns exponent (hExponent.trans_lt hc)
  rw [hb.2.2] at he
  exact he

theorem query_zero (lambda k : ℕ) : value (query (prepare lambda k) 0).number=1 := by
  have he := query_certificate lambda k 0 (Nat.zero_le _)
  simp only [pow_zero,mul_one,one_mul] at he
  exact le_antisymm he.2.2.2.2 he.2.2.2.1

theorem query_error (lambda k exponent : ℕ) (hExponent : exponent≤GeneralPaperPowerPrecision.levelBound lambda k) :
    |(geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta:ℝ)^exponent-
      (value (query (prepare lambda k) exponent).number:ℝ)|≤((GeneralPaperSourceParameters.prepare k).nu:ℝ)/1024 := by
  let base : ℚ := geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta
  let unit := (prepare lambda k).format.unit
  have hp := GeneralPaperSourceParameters.positive k
  have hb := base_bounds _ _ hp.2.1 hp.2.2.2 (GeneralPaperSourceParameters.eta_theta k)
  have hb0 : (0:ℝ)≤base := by
    have he : (0:ℚ)≤base := by dsimp only [base]; linarith [hb.1]
    exact_mod_cast he
  have hb1 : (base:ℝ)≤1 := by exact_mod_cast hb.2.le
  have hu : (0:ℝ)<unit := by
    have he : 0<unit := by dsimp only [unit,prepare]; have := GeneralPaperPowerPrecision.unit_positive lambda k; omega
    exact_mod_cast he
  have hr := retention_bounds unit (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hr0 : (0:ℝ)≤retention unit := by exact_mod_cast hr.1.le
  have hr1 : (retention unit:ℝ)≤1 := by exact_mod_cast hr.2
  have hBernoulli := GeneralPaperGeometricVariation.power_lower (retention unit:ℝ) hr0 hr1 exponent
  have hc := query_certificate lambda k exponent hExponent
  have hLower : ((retention unit)^exponent*base^exponent:ℚ)≤value (query (prepare lambda k) exponent).number := hc.2.2.2.1
  have hUpper : value (query (prepare lambda k) exponent).number≤base^exponent := hc.2.2.2.2
  have hl : (retention unit:ℝ)^exponent*(base:ℝ)^exponent≤(value (query (prepare lambda k) exponent).number:ℝ) := by
    exact_mod_cast hLower
  have hh : (value (query (prepare lambda k) exponent).number:ℝ)≤(base:ℝ)^exponent := by exact_mod_cast hUpper
  have hRet : (retention unit:ℝ)=1-1/(unit:ℝ) := by simp [retention]
  have hDef : 1-(retention unit:ℝ)=1/(unit:ℝ) := by rw [hRet]; ring
  rw [hDef] at hBernoulli
  have hBasePow : (base:ℝ)^exponent≤1 := pow_le_one₀ hb0 hb1
  have hProd := mul_le_mul_of_nonneg_right hBernoulli (pow_nonneg hb0 exponent)
  have hDivide : (1/(unit:ℝ))*(exponent:ℝ)=(exponent:ℝ)/(unit:ℝ) := by ring
  rw [hDivide] at hProd
  have hSmall := mul_nonneg (show (0:ℝ)≤(exponent:ℝ)/(unit:ℝ) by positivity) (sub_nonneg.mpr hBasePow)
  have hError : (base:ℝ)^exponent-(value (query (prepare lambda k) exponent).number:ℝ)≤(exponent:ℝ)/(unit:ℝ) := by
    have hDiff : (base:ℝ)^exponent-(value (query (prepare lambda k) exponent).number:ℝ)≤
        ((exponent:ℝ)/(unit:ℝ))*(base:ℝ)^exponent := by nlinarith only [hl,hProd]
    exact hDiff.trans (by nlinarith only [hSmall])
  have hEx : (exponent:ℝ)≤GeneralPaperPowerPrecision.levelBound lambda k := by exact_mod_cast hExponent
  have hDiv := div_le_div_of_nonneg_right hEx hu.le
  have hAccuracy : (GeneralPaperPowerPrecision.levelBound lambda k:ℝ)/(unit:ℝ)≤((GeneralPaperSourceParameters.prepare k).nu:ℝ)/1024 := by
    have he := GeneralPaperPowerPrecision.local_power_accuracy lambda k
    have hh : (((GeneralPaperPowerPrecision.levelBound lambda k:ℚ)/(GeneralPaperPowerPrecision.prepare lambda k).unit):ℝ)≤
        (((GeneralPaperSourceParameters.prepare k).nu/1024:ℚ):ℝ) := by exact_mod_cast he
    push_cast at hh
    exact hh
  rw [abs_of_nonneg (sub_nonneg.mpr hh)]
  exact hError.trans (hDiv.trans hAccuracy)

theorem query_positive (lambda k exponent : ℕ) (hExponent : exponent≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (0:ℝ)<value (query (prepare lambda k) exponent).number := by
  have he := value_positive _ (query_certificate lambda k exponent hExponent).2.2.1
  exact_mod_cast he

theorem query_work (lambda k exponent : ℕ) : (query (prepare lambda k) exponent).work≤
    (prepare lambda k).format.columns*(12*((prepare lambda k).format.fractionalBits+1)+82)+10 :=
  GeneralPaperRoundedPowerQuery.evaluate_work _ _ _ _ _

theorem prepare_work (lambda k : ℕ) : (prepare lambda k).work≤
    (GeneralPaperPowerPrecision.prepare lambda k).work+
      8*((prepare lambda k).format.fractionalBits+1-GeneralPaperStoredGeometricBase.decrementBits k)+
      (prepare lambda k).format.columns*(12*((prepare lambda k).format.fractionalBits+1)+82)+44 := by
  have hb := GeneralPaperStoredGeometricBase.construct_work (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits k
  have ht := GeneralPaperRoundedPowerTable.build_work (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits
    (prepare lambda k).format.columns (prepare lambda k).base
  change (GeneralPaperPowerPrecision.prepare lambda k).work+
    (GeneralPaperStoredGeometricBase.construct (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits k).work+
    (GeneralPaperRoundedPowerTable.build (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits
      (prepare lambda k).base (prepare lambda k).format.columns).work+24≤_
  omega

end Blotto.GeneralPaperPreparedPowers
