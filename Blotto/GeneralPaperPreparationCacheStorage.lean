import Blotto.GeneralPaperPowerConstructionStorage
import Blotto.GeneralPaperEncodedSharedParameters

/-! Literal retained front-end source controls. All five denominator
records, four rational rates, source/trajectory/profit/precision records
and auxiliary precision scalars are counted, including native work fields.
These are erased encodings of actual returns, not parameter reconstruction. -/
namespace Blotto.GeneralPaperPreparationCacheStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourcePreparationSizes
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def powerFootprint (W : ℕ) (r : GeneralPaperPowerCeiling.Result) : ℕ := fields W [r.power,r.doublings,r.work]

theorem dyadic (W m lambda k Qv e : ℕ) (he : e≤74+2*k) :
    powerFootprint W (powerRun e)≤3*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  have hp := GeneralPaperParameterOperandBounds.dyadic_word e
  have hd := power_data e
  have heW := GeneralPaperInitializerControlCounters.word_le_self e
  have hwW := GeneralPaperInitializerControlCounters.word_le_self (8*e+2)
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold powerFootprint
  apply fields_bound W _
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits GeneralPaperPowerPreparationEnvelope.operandWidth
  · omega
  · rw [hd.2.1]; omega
  · rw [hd.2.2]; omega

def denominators (W : ℕ) (c : GeneralPaperSourceParameterPrice.Cache) : ℕ :=
  powerFootprint W c.zDen+powerFootprint W c.etaDen+powerFootprint W c.nuDen+
    powerFootprint W c.thetaDen+powerFootprint W c.summaryDen+64*W

theorem denominator_bound (W m lambda k Qv : ℕ) :
    denominators W (GeneralPaperSourceParameterPrice.specification k)≤
      15*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+224*W := by
  have a := dyadic W m lambda k Qv (11+k) (by omega)
  have b := dyadic W m lambda k Qv (25+k) (by omega)
  have c := dyadic W m lambda k Qv (32+k) (by omega)
  have d := dyadic W m lambda k Qv (29+k) (by omega)
  have e := dyadic W m lambda k Qv (34+k) (by omega)
  unfold denominators GeneralPaperSourceParameterPrice.specification
  dsimp only
  omega

theorem reciprocal_word (n : ℕ) : rationalWordWidth (1/(n:ℚ))≤1+2*binaryWordWidth n := by
  simpa only [one_div] using rationalWordWidth_of_height (RationalHeight.inv (GeneralPaperBasisDivideBits.nat_height n))

theorem dyadic_rate (m lambda k Qv e : ℕ) (he : e≤74+2*k) :
    rationalWordWidth (1/((powerRun e).power:ℚ))≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := reciprocal_word (powerRun e).power
  have hp := GeneralPaperParameterOperandBounds.dyadic_word e
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

def sourceFootprint (W : ℕ) (s : GeneralPaperSourceParameters.Parameters) : ℕ :=
  rationalWordWidth s.z+rationalWordWidth s.eta+rationalWordWidth s.nu+rationalWordWidth s.theta+
    fields W [s.meshDenominator,s.summarySize,s.work]+128*W

theorem source_bound (W m lambda k Qv : ℕ) :
    sourceFootprint W (GeneralPaperSourceParameters.prepare k)≤
      7*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+163*W := by
  have a := dyadic_rate m lambda k Qv (11+k) (by omega)
  have b := dyadic_rate m lambda k Qv (25+k) (by omega)
  have c := dyadic_rate m lambda k Qv (32+k) (by omega)
  have d := dyadic_rate m lambda k Qv (29+k) (by omega)
  have ht := GeneralPaperParameterOperandBounds.dyadic_word (29+k)
  have hs := GeneralPaperParameterOperandBounds.dyadic_word (34+k)
  have hw := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).sourceWork
  have hww := GeneralPaperInitializerControlCounters.word_le_self (GeneralPaperSourceParameters.prepare k).work
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hFields : fields W [(GeneralPaperSourceParameters.prepare k).meshDenominator,
      (GeneralPaperSourceParameters.prepare k).summarySize,(GeneralPaperSourceParameters.prepare k).work]≤
        3*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
    apply fields_bound W _
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> unfold natBits GeneralPaperPowerPreparationEnvelope.operandWidth
    · change 1+binaryWordWidth (powerRun (29+k)).power≤_; omega
    · change 1+binaryWordWidth (powerRun (34+k)).power≤_; omega
    · omega
  unfold sourceFootprint
  change rationalWordWidth (1/((powerRun (11+k)).power:ℚ))+rationalWordWidth (1/((powerRun (25+k)).power:ℚ))+
    rationalWordWidth (1/((powerRun (32+k)).power:ℚ))+rationalWordWidth (1/((powerRun (29+k)).power:ℚ))+_+128*W≤_
  omega

def precisionFootprint (W : ℕ) (p : GeneralPaperPrecisionParameterPrice.Output) : ℕ :=
  GeneralPaperEncodedPreparedPowers.formatFootprint W p.parameters+fields W [p.levelBound,p.errorFactor]+64*W

theorem precision_bound (W m lambda k Qv : ℕ) :
    precisionFootprint W (GeneralPaperPrecisionParameterPrice.specification lambda k)≤
      6*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+128*W := by
  have hf := GeneralPaperEncodedPreparedPowers.format_bound W m lambda k Qv
  have hg := (GeneralPaperSourcePreparationSizes.sizes m lambda k Qv).columnsTarget
  have hGw := GeneralPaperFreshMassPrice.offset_width m lambda k Qv
  have hLambda : binaryWordWidth (lambda+1)≤GeneralPaperSourcePreparationSizes.measure m lambda k Qv := by
    unfold GeneralPaperSourcePreparationSizes.measure; omega
  have hl := GeneralPaperRayOperandWidthEnvelope.word_add (lambda+1) 1
  have h1 : binaryWordWidth 1=1 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have hProduct := binaryWordWidth_mul 16 (GeneralPaperPowerPrecision.levelBound lambda k+1)
  have hError := binaryWordWidth_mul (16*(GeneralPaperPowerPrecision.levelBound lambda k+1)) (lambda+2)
  change binaryWordWidth (GeneralPaperPowerPrecision.levelBound lambda k+1)≤32*measure m lambda k Qv at hg
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hFields : fields W [GeneralPaperPowerPrecision.levelBound lambda k,GeneralPaperPowerPrecision.errorFactor lambda k]≤
      2*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
    apply fields_bound W _
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hGw
    · unfold natBits GeneralPaperPowerPrecision.errorFactor GeneralPaperPowerPreparationEnvelope.operandWidth
      have he : lambda+1+1=lambda+2 := by omega
      rw [he] at hl
      omega
  unfold precisionFootprint GeneralPaperPrecisionParameterPrice.specification
  dsimp only
  omega

def footprint (W : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) : ℕ :=
  denominators W c.denominators+sourceFootprint W c.source+
    GeneralPaperEncodedSharedParameters.trajectoryFootprint W c.trajectory+
    GeneralPaperEncodedSharedParameters.profitFootprint W c.profit+precisionFootprint W c.precision+128*W

def profile (W m lambda k Qv : ℕ) : ℕ :=
  39*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+843*W

theorem native (W m lambda k Qv : ℕ) :
    footprint W (GeneralPaperSourcePreparationCache.specification m lambda k Qv)≤profile W m lambda k Qv := by
  have a := denominator_bound W m lambda k Qv
  have b := source_bound W m lambda k Qv
  have c := GeneralPaperEncodedSharedParameters.trajectory W m lambda k Qv
  have d := GeneralPaperEncodedSharedParameters.profit W m lambda k Qv
  have e := precision_bound W m lambda k Qv
  unfold footprint profile GeneralPaperSourcePreparationCache.specification
  dsimp only
  omega

theorem returned (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    footprint W (GeneralPaperSourcePreparationCache.prepare primitive W m lambda k Qv).1≤profile W m lambda k Qv := by
  rw [GeneralPaperSourcePreparationCache.data]
  exact native W m lambda k Qv

end Blotto.GeneralPaperPreparationCacheStorage
