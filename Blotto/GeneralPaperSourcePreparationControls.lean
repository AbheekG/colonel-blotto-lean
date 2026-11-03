import Blotto.GeneralPaperSourcePreparationEnvelope

/-! One derived local word for all reached parameter-constructor controls.
Large dyadic/row/grid values retain their arithmetic operand prices. The
new word covers loop counters and native metadata, not future source-array
addresses or retained global objects. Calibration is analytical only.
-/
namespace Blotto.GeneralPaperSourcePreparationControls
open GeneralPaperSourcePreparationSizes GeneralPaperSourcePreparationEnvelope
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def word (m lambda k Qv : ℕ) : ℕ := 256+16*binaryWordWidth (measure m lambda k Qv+1)
def cap (m lambda k Qv : ℕ) : ℕ := 65536*(measure m lambda k Qv+1)

theorem bounded (m lambda k Qv n : ℕ) (hn : n≤cap m lambda k Qv) : binaryWordWidth n≤word m lambda k Qv := by
  have hm := binaryWordWidth_mul 65536 (measure m lambda k Qv+1)
  have hs := binaryWordWidth_mono hn
  have h65536 : binaryWordWidth 65536=17 := by decide
  unfold cap at hn
  change binaryWordWidth n≤binaryWordWidth (65536*(measure m lambda k Qv+1)) at hs
  unfold word
  omega

def IsTarget (m lambda k Qv target : ℕ) : Prop :=
  target=m ∨ target=GeneralPaperTrajectoryParameterPrice.target lambda k ∨
  target=GeneralPaperProfitParameterPrice.widthTarget m k ∨
  target=4*(2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*Qv*(GeneralPaperSourceParameters.prepare k).meshDenominator) ∨
  target=GeneralPaperPrecisionParameterPrice.target lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power ∨
  target=GeneralPaperPrecisionParameterPrice.level (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator+1

theorem target_word (m lambda k Qv target : ℕ) (h : IsTarget m lambda k Qv target) :
    binaryWordWidth target≤128*measure m lambda k Qv := by
  have hb := sizes m lambda k Qv
  rcases h with h|h|h|h|h|h <;> rw [h]
  · have hm := binaryWordWidth_mono (show m≤m+1 by omega)
    unfold GeneralPaperSourcePreparationSizes.measure
    omega
  · have hh:=hb.trajectoryTarget; omega
  · have hh:=hb.profitWidthTarget; omega
  · have hh:=hb.profitExponentTarget; omega
  · exact hb.precisionTarget
  · have hh:=hb.columnsTarget; omega

theorem dyadic_controls (primitive : ℕ → ℕ) (m lambda k Qv e : ℕ) (he : e≤74+2*k) :
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m lambda k Qv) e).1.doublings+1)≤word m lambda k Qv ∧
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m lambda k Qv) e).1.work+8)≤word m lambda k Qv := by
  have hBase := (base m lambda k Qv).1
  have hIndex : 74+2*k+1≤2*(measure m lambda k Qv+1) := by omega
  have hi := binaryWordWidth_mono hIndex
  have hm := binaryWordWidth_mul 2 (measure m lambda k Qv+1)
  have h2 : binaryWordWidth 2=2 := by decide
  apply GeneralPaperParameterCounterWords.dyadic_prefix primitive _ (74+2*k) e he
  unfold word
  omega

theorem ceiling_controls (primitive : ℕ → ℕ) (m lambda k Qv target p : ℕ) (hp : 0<p)
    (ht : IsTarget m lambda k Qv target) :
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m lambda k Qv) target p hp).1.doublings+1)≤word m lambda k Qv ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m lambda k Qv) target p hp).1.work+192)≤word m lambda k Qv := by
  have hT := target_word m lambda k Qv target ht
  have hIndex : binaryWordWidth target+1≤256*(measure m lambda k Qv+1) := by omega
  have hi := binaryWordWidth_mono hIndex
  have hm := binaryWordWidth_mul 256 (measure m lambda k Qv+1)
  have h256 : binaryWordWidth 256=9 := by decide
  apply GeneralPaperParameterCounterWords.ceiling
  unfold word
  omega

structure Metadata (m lambda k Qv : ℕ) : Prop where
  sourceWork : (GeneralPaperSourceParameters.prepare k).work≤512*measure m lambda k Qv
  trajectoryWork : (GeneralPaperTrajectoryParameters.prepare lambda k).work≤512*measure m lambda k Qv
  profitWork : (GeneralPaperProfitParameters.parameters m lambda k Qv).parameterWork≤4096*measure m lambda k Qv
  precisionWork : (GeneralPaperPowerPrecision.prepare lambda k).work≤8192*measure m lambda k Qv
  rowBits : (GeneralPaperTrajectoryParameters.prepare lambda k).rowBits≤8*measure m lambda k Qv
  height : (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤measure m lambda k Qv
  exponent : (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent≤32*measure m lambda k Qv
  fractionalBits : (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits≤128*measure m lambda k Qv
  columns : (GeneralPaperPowerPrecision.prepare lambda k).columns≤32*measure m lambda k Qv
  comparison : GeneralPaperQuantileComparison.width lambda k≤256*measure m lambda k Qv

theorem metadata (m lambda k Qv : ℕ) : Metadata m lambda k Qv := by
  let M := measure m lambda k Qv
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  have hb := sizes m lambda k Qv
  have hBase := (base m lambda k Qv).1
  have hm := binaryWordWidth_mono (show m≤m+1 by omega)
  have hDim : binaryWordWidth m≤M := by dsimp [M,GeneralPaperSourcePreparationSizes.measure]; omega
  have hs := GeneralPaperSourceParameters.prepare_work k
  have hS : s.work≤512*M := by change s.work=8*(131+5*k)+74 at hs; omega
  have ht := GeneralPaperTrajectoryParameters.prepare_work lambda k
  rw [←(power_data (35+k)).1] at ht
  change t.work≤8*(11+k)+8*(35+k)+12*binaryWordWidth (GeneralPaperTrajectoryParameterPrice.target lambda k)+30 at ht
  have hT : t.work≤512*M := by have hh:=hb.trajectoryTarget; change _≤4*M at hh; omega
  have hl := GeneralPaperPowerCeiling.ceiling_work m
  have hw := GeneralPaperPowerCeiling.ceiling_work (GeneralPaperProfitParameterPrice.widthTarget m k)
  have he := GeneralPaperPowerCeiling.ceiling_work (4*(2*t.rows*Qv*s.meshDenominator))
  have ha := (power_data (25+k)).2.2
  have hP : p.parameterWork≤4096*M := by
    have hW := hb.profitWidthTarget
    have hE := hb.profitExponentTarget
    change _≤8*M at hW
    change binaryWordWidth (4*(2*t.rows*Qv*s.meshDenominator))≤32*M at hE
    change s.work+t.work+(GeneralPaperPowerCeiling.ceiling m).work+(powerRun (25+k)).work+
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperProfitParameterPrice.widthTarget m k)).work+
      (GeneralPaperPowerCeiling.ceiling (4*(2*t.rows*Qv*s.meshDenominator))).work+64≤4096*M
    omega
  have hf := GeneralPaperPowerPrecision.prepare_work lambda k
  rw [←(power_data (74+2*k)).1,←(power_data (32+k)).1] at hf
  change f.work≤8*(32+k)+8*(74+2*k)+12*binaryWordWidth
    (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum)+
    12*binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)+s.work+t.work+72 at hf
  have hF : f.work≤8192*M := by
    have hP := hb.precisionTarget
    have hC := hb.columnsTarget
    change binaryWordWidth (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum)≤128*M at hP
    change binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)≤32*M at hC
    omega
  have hRow := GeneralPaperTrajectoryParameters.rowBits_bound lambda k
  rw [←(power_data (35+k)).1] at hRow
  change t.rowBits≤binaryWordWidth (GeneralPaperTrajectoryParameterPrice.target lambda k)+(11+k) at hRow
  have hR : t.rowBits≤8*M := by have hh:=hb.trajectoryTarget; change _≤4*M at hh; omega
  have hHeight := GeneralPaperPowerCeiling.loop_depth m 1 (by decide)
  change p.height≤binaryWordWidth m at hHeight
  have hE := GeneralPaperPowerCeiling.loop_depth (4*(2*t.rows*Qv*s.meshDenominator)) 1 (by decide)
  change p.exponent≤binaryWordWidth (4*(2*t.rows*Qv*s.meshDenominator)) at hE
  have hBits := GeneralPaperPowerPrecision.bits_upper lambda k
  rw [←(power_data (74+2*k)).1,←(power_data (32+k)).1] at hBits
  change f.fractionalBits≤binaryWordWidth (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum) at hBits
  have hCols := GeneralPaperPowerPrecision.columns_upper lambda k
  change f.columns≤binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1) at hCols
  have hExp := hb.profitExponentTarget
  have hPrec := hb.precisionTarget
  have hCol := hb.columnsTarget
  change binaryWordWidth (4*(2*t.rows*Qv*s.meshDenominator))≤32*M at hExp
  change binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)≤32*M at hCol
  change binaryWordWidth (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum)≤128*M at hPrec
  have hComparison : GeneralPaperQuantileComparison.width lambda k≤256*M := by
    change f.fractionalBits+1+(34+k)≤256*M
    omega
  exact ⟨hS,hT,hP,hF,hR,hHeight.trans hDim,hE.trans hExp,hBits.trans hPrec,hCols.trans hCol,hComparison⟩

theorem metadata_words (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    let c := (GeneralPaperSourcePreparationCache.prepare primitive W m lambda k Qv).1
    binaryWordWidth (c.source.work+128)≤word m lambda k Qv ∧
      binaryWordWidth (c.trajectory.work+128)≤word m lambda k Qv ∧
      binaryWordWidth (c.profit.parameterWork+128)≤word m lambda k Qv ∧
      binaryWordWidth (c.precision.parameters.work+128)≤word m lambda k Qv ∧
      binaryWordWidth (c.trajectory.rowBits+1)≤word m lambda k Qv ∧
      binaryWordWidth (c.profit.height+1)≤word m lambda k Qv ∧
      binaryWordWidth (c.profit.exponent+1)≤word m lambda k Qv ∧
      binaryWordWidth (c.precision.parameters.fractionalBits+1)≤word m lambda k Qv ∧
      binaryWordWidth (c.precision.parameters.columns+1)≤word m lambda k Qv ∧
      binaryWordWidth (GeneralPaperQuantileComparison.width lambda k+1)≤word m lambda k Qv := by
  rw [GeneralPaperSourcePreparationCache.data]
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  have h := metadata m lambda k Qv
  have hs := h.sourceWork
  have ht := h.trajectoryWork
  have hp := h.profitWork
  have hf := h.precisionWork
  have hr := h.rowBits
  have hh := h.height
  have he := h.exponent
  have hb := h.fractionalBits
  have hc := h.columns
  have hq := h.comparison
  refine ⟨bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,
    bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,
    bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_,bounded m lambda k Qv _ ?_⟩ <;>
    unfold cap <;> omega

theorem word_le_operand_width (m lambda k Qv : ℕ) : word m lambda k Qv≤width m lambda k Qv := by
  have hm := GeneralPaperInitializerControlCounters.word_le_self (measure m lambda k Qv+1)
  have hp := (base m lambda k Qv).2
  unfold word width
  omega

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare model.rat (word m lambda k Qv) m lambda k Qv).2≤
      524288*measure m lambda k Qv*model.rat (width m lambda k Qv) := by
  have h := GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone (word m lambda k Qv) m lambda k Qv
  have hw := (word_le_operand_width m lambda k Qv).trans (model.word_le (width m lambda k Qv))
  calc
    _ ≤ 262144*measure m lambda k Qv*(word m lambda k Qv+model.rat (width m lambda k Qv)) := h
    _ ≤ 262144*measure m lambda k Qv*(2*model.rat (width m lambda k Qv)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end Blotto.GeneralPaperSourcePreparationControls
