import Blotto.GeneralPaperEncodedProfitGrid

/-! Retained trajectory/profit parameter scalars, including native work.
The complete prepared profit object also owns both encoded grid arrays. -/
namespace Blotto.GeneralPaperEncodedSharedParameters
open GeneralPaperEncodedScalarStorage GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def trajectoryFootprint (W : ℕ) (t : GeneralPaperTrajectoryParameters.Parameters) : ℕ :=
  fields W [t.period,t.epochs,t.rows,t.rowBits,t.work]

theorem trajectory (W m lambda k Qv : ℕ) :
    trajectoryFootprint W (GeneralPaperTrajectoryParameters.prepare lambda k)≤
      5*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hr : t.rows=t.epochs*t.period := rfl
  have hp : 0<t.period := by
    change 0<(GeneralPaperTrajectoryParameters.prepare lambda k).period
    rw [GeneralPaperTrajectoryParameters.period_power]
    positivity
  have he : 0<t.epochs := by
    have hrows := GeneralPaperTrajectoryParameters.rows_positive lambda k
    change 0<t.rows at hrows
    nlinarith only [hr,hrows]
  have hpr : t.period≤t.rows := by nlinarith only [hp,he,hr]
  have her : t.epochs≤t.rows := by nlinarith only [hp,he,hr]
  have hrows := (GeneralPaperSourcePreparationSizes.sizes m lambda k Qv).rows
  change binaryWordWidth t.rows≤8*M at hrows
  have hperiod := binaryWordWidth_mono hpr
  have hepoch := binaryWordWidth_mono her
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hbits := hm.rowBits
  have hwork := hm.trajectoryWork
  change t.rowBits≤8*M at hbits
  change t.work≤512*M at hwork
  have hbw := GeneralPaperInitializerControlCounters.word_le_self t.rowBits
  have hww := GeneralPaperInitializerControlCounters.word_le_self t.work
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change fields W [t.period,t.epochs,t.rows,t.rowBits,t.work]≤_
  apply fields_bound W H
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> unfold natBits H GeneralPaperPowerPreparationEnvelope.operandWidth <;> omega

def profitFootprint (W : ℕ) (p : GeneralPaperProfitParameters.Parameters) : ℕ :=
  fields W [p.height,p.leafCount,p.qProf,p.width,p.exponent,p.parameterWork]

theorem profit (W m lambda k Qv : ℕ) :
    profitFootprint W (GeneralPaperProfitParameters.parameters m lambda k Qv)≤
      6*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hh := hm.height
  have he := hm.exponent
  have hp := hm.profitWork
  change p.height≤M at hh
  change p.exponent≤32*M at he
  change p.parameterWork≤4096*M at hp
  have hs := GeneralPaperProfitGridEnvelope.sizes m lambda k Qv
  have hq := hs.q
  have hw := hs.width
  change binaryWordWidth p.qProf≤32*M at hq
  change binaryWordWidth (p.width+1)≤16*M at hw
  have hw' := binaryWordWidth_mono (show p.width≤p.width+1 by omega)
  have hl := GeneralPaperNatPowerOperands.power_width 2 p.height
  rw [←GeneralPaperProfitParameters.leaf_count_spec m lambda k Qv] at hl
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hl
  change binaryWordWidth p.leafCount≤1+p.height*2 at hl
  have hhw := GeneralPaperInitializerControlCounters.word_le_self p.height
  have hew := GeneralPaperInitializerControlCounters.word_le_self p.exponent
  have hpw := GeneralPaperInitializerControlCounters.word_le_self p.parameterWork
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change fields W [p.height,p.leafCount,p.qProf,p.width,p.exponent,p.parameterWork]≤_
  apply fields_bound W H
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold natBits H GeneralPaperPowerPreparationEnvelope.operandWidth <;> omega

def preparedProfitFootprint (W : ℕ) (p : GeneralPaperProfitParameters.Prepared) : ℕ :=
  profitFootprint W p.parameters+GeneralPaperEncodedProfitGrid.footprint W p.grid+64*W

def preparedProfitProfile (W m lambda k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  6*(H+W)+GeneralPaperEncodedProfitGrid.profile W H p.width p.exponent+96*W

theorem prepared_profit (W m lambda k Qv : ℕ) :
    preparedProfitFootprint W (GeneralPaperProfitParameters.prepare m lambda k Qv)≤preparedProfitProfile W m lambda k Qv := by
  have hp := profit W m lambda k Qv
  have hg := GeneralPaperEncodedProfitGrid.source W m lambda k Qv
  unfold preparedProfitFootprint preparedProfitProfile
  dsimp only
  change profitFootprint W (GeneralPaperProfitParameters.parameters m lambda k Qv)+
    GeneralPaperEncodedProfitGrid.footprint W (GeneralPaperProfitParameters.prepare m lambda k Qv).grid+64*W≤_
  have hgrid : GeneralPaperEncodedProfitGrid.footprint W (GeneralPaperProfitParameters.prepare m lambda k Qv).grid≤
      GeneralPaperEncodedProfitGrid.profile W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
        (GeneralPaperProfitParameters.parameters m lambda k Qv).width
        (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent := hg
  omega

end Blotto.GeneralPaperEncodedSharedParameters
