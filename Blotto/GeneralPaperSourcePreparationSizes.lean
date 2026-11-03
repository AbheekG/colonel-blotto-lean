import Blotto.GeneralPaperSourcePreparationCache

/-! Actual constructor operands are logarithmic in the horizon/alphabet,
dimension and rounded-value denominator, and linear in the accuracy index.
The envelope is derived from the constructor definitions, including raw
products/maxima and zero-target ceilings, rather than supplied by a caller.
-/
namespace Blotto.GeneralPaperSourcePreparationSizes
open GeneralPaperParameterOperandBounds GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def measure (m lambda k Qv : ℕ) : ℕ :=
  128+k+binaryWordWidth (lambda+1)+binaryWordWidth (m+1)+binaryWordWidth (Qv+1)

def width (m lambda k Qv : ℕ) : ℕ := 4096*measure m lambda k Qv

structure Sizes (m lambda k Qv : ℕ) : Prop where
  source : GeneralPaperSourceParameterPrice.width k≤width m lambda k Qv
  dyadic : 8+2*(74+2*k)≤width m lambda k Qv
  trajectoryTarget : binaryWordWidth (GeneralPaperTrajectoryParameterPrice.target lambda k)≤4*measure m lambda k Qv
  trajectoryRaw : GeneralPaperTrajectoryParameterPrice.rawWidth lambda k
    (powerRun (11+k)).power (powerRun (35+k)).power
    (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).power
    (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).doublings
    (powerRun (11+k)).doublings≤width m lambda k Qv
  rows : binaryWordWidth (GeneralPaperTrajectoryParameters.prepare lambda k).rows≤8*measure m lambda k Qv
  profitWidthTarget : binaryWordWidth (GeneralPaperProfitParameterPrice.widthTarget m k)≤8*measure m lambda k Qv
  profitExponentTarget : binaryWordWidth (4*(2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*Qv*
    (GeneralPaperSourceParameters.prepare k).meshDenominator))≤32*measure m lambda k Qv
  profitRaw : GeneralPaperProfitParameterPrice.rawWidth m Qv (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator (GeneralPaperPowerCeiling.ceiling m).doublings
    (powerRun (25+k)).power≤width m lambda k Qv
  precisionTarget : binaryWordWidth (GeneralPaperPrecisionParameterPrice.target lambda
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows (GeneralPaperSourceParameters.prepare k).meshDenominator
    (powerRun (32+k)).power (powerRun (74+2*k)).power)≤128*measure m lambda k Qv
  columnsTarget : binaryWordWidth (GeneralPaperPrecisionParameterPrice.level
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows (GeneralPaperSourceParameters.prepare k).meshDenominator+1)≤32*measure m lambda k Qv
  precisionRaw : GeneralPaperPrecisionParameterPrice.rawWidth lambda k
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows (GeneralPaperSourceParameters.prepare k).meshDenominator
    (powerRun (32+k)).power (powerRun (74+2*k)).power≤width m lambda k Qv

theorem sizes (m lambda k Qv : ℕ) : Sizes m lambda k Qv := by
  let M := measure m lambda k Qv
  let H := width m lambda k Qv
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let p := powerRun (11+k)
  let f := powerRun (35+k)
  let e := GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)
  let h := (GeneralPaperPowerCeiling.ceiling m).doublings
  let alpha := (powerRun (25+k)).power
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  have hBase : k+128≤M := by dsimp [M,measure]; omega
  have hPos : 128≤M := by omega
  have hl := binaryWordWidth_mono (show lambda≤lambda+1 by omega)
  have hm := binaryWordWidth_mono (show m≤m+1 by omega)
  have hq := binaryWordWidth_mono (show Qv≤Qv+1 by omega)
  have hLam : binaryWordWidth lambda≤M := by dsimp [M,measure]; omega
  have hDim : binaryWordWidth m≤M := by dsimp [M,measure]; omega
  have hQv : binaryWordWidth Qv≤M := by dsimp [M,measure]; omega
  have hk : binaryWordWidth k≤M := (GeneralPaperInitializerControlCounters.word_le_self k).trans (by omega)
  have hp : binaryWordWidth p.power≤2*M := by have hh:=dyadic_word (11+k); change _≤2*M; dsimp only [p]; omega
  have hf : binaryWordWidth f.power≤2*M := by have hh:=dyadic_word (35+k); change _≤2*M; dsimp only [f]; omega
  have hMesh : binaryWordWidth s.meshDenominator≤2*M := by
    have hh := dyadic_word (29+k)
    change binaryWordWidth (powerRun (29+k)).power≤2*M
    omega
  have hAlpha : binaryWordWidth alpha≤2*M := by have hh:=dyadic_word (25+k); dsimp only [alpha]; omega
  have hNu : binaryWordWidth nu≤2*M := by have hh:=dyadic_word (32+k); dsimp only [nu]; omega
  have hMin : binaryWordWidth minimum≤4*M := by have hh:=dyadic_word (74+2*k); dsimp only [minimum]; omega
  have hLambdaPlus := GeneralPaperRayOperandWidthEnvelope.word_add lambda 2
  have h2 : binaryWordWidth 2=2 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have h4 : binaryWordWidth 4=3 := by decide
  have h8 : binaryWordWidth 8=4 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  have hT := binaryWordWidth_mul (lambda+2) f.power
  have hTarget : binaryWordWidth (GeneralPaperTrajectoryParameterPrice.target lambda k)≤4*M := by
    change binaryWordWidth ((lambda+2)*f.power)≤4*M
    omega
  have hEp := ceiling_word (GeneralPaperTrajectoryParameterPrice.target lambda k)
  change binaryWordWidth e.power≤_ at hEp
  have hEd := ceiling_depth_word (GeneralPaperTrajectoryParameterPrice.target lambda k)
  change binaryWordWidth e.doublings≤_ at hEd
  have hPd : binaryWordWidth p.doublings≤M := by
    dsimp only [p]
    rw [(power_data (11+k)).2.1]
    exact (GeneralPaperInitializerControlCounters.word_le_self (11+k)).trans (by omega)
  have hRows := binaryWordWidth_mul e.power p.power
  change binaryWordWidth t.rows≤binaryWordWidth e.power+binaryWordWidth p.power at hRows
  have hRowBound : binaryWordWidth t.rows≤8*M := by omega
  have hHeight := ceiling_depth_word m
  change binaryWordWidth h≤_ at hHeight
  have hHeightPlus := GeneralPaperRayOperandWidthEnvelope.word_add h 1
  have hW1 := binaryWordWidth_mul 4 (h+1)
  have hW2 := binaryWordWidth_mul (4*(h+1)) alpha
  have hWidthTarget : binaryWordWidth (GeneralPaperProfitParameterPrice.widthTarget m k)≤8*M := by
    change binaryWordWidth (4*(h+1)*alpha)≤8*M
    omega
  have hQ1 := binaryWordWidth_mul 2 t.rows
  have hQ2 := binaryWordWidth_mul (2*t.rows) Qv
  have hQ3 := binaryWordWidth_mul (2*t.rows*Qv) s.meshDenominator
  have hQ : binaryWordWidth (2*t.rows*Qv*s.meshDenominator)≤16*M := by omega
  have hQ4 := binaryWordWidth_mul 4 (2*t.rows*Qv*s.meshDenominator)
  have hExp : binaryWordWidth (4*(2*t.rows*Qv*s.meshDenominator))≤32*M := by omega
  have hG1 := binaryWordWidth_mul 8 t.rows
  have hG2 := binaryWordWidth_mul (8*t.rows) s.meshDenominator
  have hLevel : binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator)≤16*M := by
    change binaryWordWidth (8*t.rows*s.meshDenominator)≤16*M
    omega
  have hGP := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator) 1
  have hColumns : binaryWordWidth (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)≤32*M := by omega
  have hE1 := binaryWordWidth_mul 16 (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)
  have hE2 := binaryWordWidth_mul (16*(GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)) (lambda+2)
  have hError : binaryWordWidth (GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator)≤32*M := by
    change binaryWordWidth (16*(GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1)*(lambda+2))≤32*M
    omega
  have hN1 := binaryWordWidth_mul 64 (GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator)
  have hN2 := binaryWordWidth_mul (64*GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator) nu
  have hMax := max_word minimum (64*GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator*nu)
  have hPrecision : binaryWordWidth (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum)≤128*M := by
    change binaryWordWidth (max minimum (64*GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator*nu))≤128*M
    omega
  have hSource : GeneralPaperSourceParameterPrice.width k≤H := by dsimp [GeneralPaperSourceParameterPrice.width,H,width]; omega
  have hDyadic : 8+2*(74+2*k)≤H := by dsimp [H,width]; omega
  have hTRaw : GeneralPaperTrajectoryParameterPrice.rawWidth lambda k p.power f.power e.power e.doublings p.doublings≤H := by
    dsimp [GeneralPaperTrajectoryParameterPrice.rawWidth,H,width]
    omega
  have hPRaw : GeneralPaperProfitParameterPrice.rawWidth m Qv t.rows s.meshDenominator h alpha≤H := by
    dsimp [GeneralPaperProfitParameterPrice.rawWidth,H,width]
    omega
  have hFRaw : GeneralPaperPrecisionParameterPrice.rawWidth lambda k t.rows s.meshDenominator nu minimum≤H := by
    dsimp [GeneralPaperPrecisionParameterPrice.rawWidth,H,width]
    omega
  exact ⟨hSource,hDyadic,hTarget,hTRaw,hRowBound,hWidthTarget,hExp,hPRaw,hPrecision,hColumns,hFRaw⟩

end Blotto.GeneralPaperSourcePreparationSizes
