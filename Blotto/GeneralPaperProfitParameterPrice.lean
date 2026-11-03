import Blotto.GeneralPaperTrajectoryParameterPrice

/-! Profit parameters from retained source/trajectory controls. Only the
three new ceilings and displayed arithmetic execute; source, trajectory
and alpha-denominator constructors are reused. Native metadata stays exact.
Profit-grid materialization and optimizer execution have separate prices.
-/
namespace Blotto.GeneralPaperProfitParameterPrice
open GeneralPaperParameterOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def rawWidth (m Qv rows mesh height alpha : ℕ) : ℕ :=
  64+8*(binaryWordWidth m+binaryWordWidth Qv+binaryWordWidth rows+
    binaryWordWidth mesh+binaryWordWidth height+binaryWordWidth alpha)

def rawWork (primitive : ℕ → ℕ) (Qv rows mesh height alpha : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 rows+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (2*rows) Qv+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (2*rows*Qv) mesh+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) height 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 4 (height+1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (4*(height+1)) alpha+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 4 (2*rows*Qv*mesh)

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m Qv rows mesh height alpha : ℕ) :
    rawWork primitive Qv rows mesh height alpha≤14*primitive (rawWidth m Qv rows mesh height alpha) := by
  let L := rawWidth m Qv rows mesh height alpha
  have hA := binaryWordWidth_mul 2 rows
  have hB := binaryWordWidth_mul (2*rows) Qv
  have hC := binaryWordWidth_mul (2*rows*Qv) mesh
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add height 1
  have hE := binaryWordWidth_mul 4 (height+1)
  have hF := binaryWordWidth_mul (4*(height+1)) alpha
  have hG := binaryWordWidth_mul 4 (2*rows*Qv*mesh)
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h4 : binaryWordWidth 4=3 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 rows L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (2*rows) Qv L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (2*rows*Qv) mesh L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) height 1 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 4 (height+1) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hf := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (4*(height+1)) alpha L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hg := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 4 (2*rows*Qv*mesh) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  change _≤14*primitive L
  unfold rawWork
  omega

def fromCache (primitive : ℕ → ℕ) (W m Qv : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (s : GeneralPaperSourceParameters.Parameters) (t : GeneralPaperTrajectoryParameters.Parameters) :
    GeneralPaperProfitParameters.Parameters × ℕ :=
  let leaves := GeneralPaperPowerCeilingBits.run primitive W m
  let q := 2*t.rows*Qv*s.meshDenominator
  let w := GeneralPaperPowerCeilingBits.run primitive W (4*(leaves.1.doublings+1)*c.etaDen.power)
  let exponent := GeneralPaperPowerCeilingBits.run primitive W (4*q)
  (⟨leaves.1.doublings,leaves.1.power,q,w.1.power,exponent.1.doublings,
    s.work+t.work+leaves.1.work+c.etaDen.work+w.1.work+exponent.1.work+64⟩,
    leaves.2+w.2+exponent.2+rawWork primitive Qv t.rows s.meshDenominator leaves.1.doublings c.etaDen.power+128*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (hc : c=GeneralPaperSourceParameterPrice.specification k) (s : GeneralPaperSourceParameters.Parameters)
    (hs : s=GeneralPaperSourceParameters.prepare k) (t : GeneralPaperTrajectoryParameters.Parameters)
    (ht : t=GeneralPaperTrajectoryParameters.prepare lambda k) :
    (fromCache primitive W m Qv c s t).1=GeneralPaperProfitParameters.parameters m lambda k Qv := by
  subst c; subst s; subst t
  simp only [fromCache,GeneralPaperPowerCeilingBits.data,GeneralPaperSourceParameterPrice.specification,
    GeneralPaperProfitParameters.parameters]

def widthTarget (m k : ℕ) : ℕ :=
  4*((GeneralPaperPowerCeiling.ceiling m).doublings+1)*(GeneralPaperScoreScaleParameters.powerRun (25+k)).power

def profile (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let h := (GeneralPaperPowerCeiling.ceiling m).doublings
  let alpha := (GeneralPaperScoreScaleParameters.powerRun (25+k)).power
  ceilingProfile primitive W m+ceilingProfile primitive W (widthTarget m k)+
    ceilingProfile primitive W (4*(2*t.rows*Qv*s.meshDenominator))+
    14*primitive (rawWidth m Qv t.rows s.meshDenominator h alpha)+128*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperSourceParameterPrice.Cache) (hc : c=GeneralPaperSourceParameterPrice.specification k)
    (s : GeneralPaperSourceParameters.Parameters) (hs : s=GeneralPaperSourceParameters.prepare k)
    (t : GeneralPaperTrajectoryParameters.Parameters) (ht : t=GeneralPaperTrajectoryParameters.prepare lambda k) :
    (fromCache primitive W m Qv c s t).2≤profile primitive W m lambda k Qv := by
  subst c; subst s; subst t
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let h := (GeneralPaperPowerCeiling.ceiling m).doublings
  let alpha := (GeneralPaperScoreScaleParameters.powerRun (25+k)).power
  have hl := ceiling_work primitive hMono W m
  have hw := ceiling_work primitive hMono W (widthTarget m k)
  have he := ceiling_work primitive hMono W (4*(2*t.rows*Qv*s.meshDenominator))
  have hr := raw_work primitive hMono m Qv t.rows s.meshDenominator h alpha
  unfold fromCache profile
  dsimp only
  rw [GeneralPaperPowerCeilingBits.data]
  change (GeneralPaperPowerCeilingBits.run primitive W m).2+
    (GeneralPaperPowerCeilingBits.run primitive W (widthTarget m k)).2+
    (GeneralPaperPowerCeilingBits.run primitive W (4*(2*t.rows*Qv*s.meshDenominator))).2+
    rawWork primitive Qv t.rows s.meshDenominator h alpha+128*W≤_
  dsimp only [s,t,h,alpha] at *
  omega

end Blotto.GeneralPaperProfitParameterPrice
