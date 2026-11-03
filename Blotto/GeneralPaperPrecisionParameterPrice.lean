import Blotto.GeneralPaperProfitParameterPrice

/-! Precision controls consume the same retained source/trajectory records.
The nu denominator is reused. The minimum dyadic, both new ceilings and
all raw arithmetic/max/result writes are priced. G and E are returned for
later source callers, rather than reconstructed in an annotation pass.
-/
namespace Blotto.GeneralPaperPrecisionParameterPrice
open GeneralPaperParameterOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def level (rows mesh : ℕ) : ℕ := 8*rows*mesh
def error (lambda rows mesh : ℕ) : ℕ := 16*(level rows mesh+1)*(lambda+2)
def target (lambda rows mesh nu minimum : ℕ) : ℕ := max minimum (64*error lambda rows mesh*nu)

structure Output where
  parameters : GeneralPaperPowerPrecision.Parameters
  levelBound : ℕ
  errorFactor : ℕ

def specification (lambda k : ℕ) : Output :=
  ⟨GeneralPaperPowerPrecision.prepare lambda k,GeneralPaperPowerPrecision.levelBound lambda k,
    GeneralPaperPowerPrecision.errorFactor lambda k⟩

def rawWidth (lambda k rows mesh nu minimum : ℕ) : ℕ :=
  128+16*(binaryWordWidth lambda+binaryWordWidth k+binaryWordWidth rows+
    binaryWordWidth mesh+binaryWordWidth nu+binaryWordWidth minimum)

def rawWork (primitive : ℕ → ℕ) (lambda k rows mesh nu minimum : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 8 rows+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (8*rows) mesh+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (level rows mesh) 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) lambda 2+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 16 (level rows mesh+1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (16*(level rows mesh+1)) (lambda+2)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 74 (2*k)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 64 (error lambda rows mesh)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (64*error lambda rows mesh) nu+
  GeneralPaperIntegerWordPrice.compare primitive minimum (64*error lambda rows mesh*nu)+
  primitive (1+binaryWordWidth (target lambda rows mesh nu minimum))

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (lambda k rows mesh nu minimum : ℕ) :
    rawWork primitive lambda k rows mesh nu minimum≤22*primitive (rawWidth lambda k rows mesh nu minimum) := by
  let L := rawWidth lambda k rows mesh nu minimum
  have hA := binaryWordWidth_mul 8 rows
  have hB := binaryWordWidth_mul (8*rows) mesh
  have hC := GeneralPaperRayOperandWidthEnvelope.word_add (level rows mesh) 1
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add lambda 2
  have hE := binaryWordWidth_mul 16 (level rows mesh+1)
  have hF := binaryWordWidth_mul (16*(level rows mesh+1)) (lambda+2)
  have hG := binaryWordWidth_mul 2 k
  have hH := GeneralPaperRayOperandWidthEnvelope.word_add 74 (2*k)
  have hI := binaryWordWidth_mul 64 (error lambda rows mesh)
  have hJ := binaryWordWidth_mul (64*error lambda rows mesh) nu
  have hM := max_word minimum (64*error lambda rows mesh*nu)
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h8 : binaryWordWidth 8=4 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  have h74 : binaryWordWidth 74=7 := by decide
  dsimp only [level,error] at hC hE hF hI hJ hM
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 8 rows L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (8*rows) mesh L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (level rows mesh) 1 L
    (by dsimp [L,rawWidth,level]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,level]; omega)
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) lambda 2 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 16 (level rows mesh+1) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,level]; omega) (by dsimp [L,rawWidth,level]; omega)
  have hf := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (16*(level rows mesh+1)) (lambda+2) L
    (by dsimp [L,rawWidth,level]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,level]; omega)
  have hg := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 k L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hh := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 74 (2*k) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hi := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 64 (error lambda rows mesh) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,error,level]; omega) (by dsimp [L,rawWidth,error,level]; omega)
  have hj := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (64*error lambda rows mesh) nu L
    (by dsimp [L,rawWidth,error,level]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,error,level]; omega)
  have hm := GeneralPaperIntegerWordPrice.compare_le primitive hMono minimum (64*error lambda rows mesh*nu) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth,error,level]; omega)
  have hw := hMono (show 1+binaryWordWidth (target lambda rows mesh nu minimum)≤L by dsimp [L,rawWidth,target,error,level]; omega)
  change _≤22*primitive L
  unfold rawWork
  omega

def fromCache (primitive : ℕ → ℕ) (W lambda k : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (s : GeneralPaperSourceParameters.Parameters) (t : GeneralPaperTrajectoryParameters.Parameters) : Output × ℕ :=
  let G := level t.rows s.meshDenominator
  let E := error lambda t.rows s.meshDenominator
  let minimum := GeneralPaperDyadicPowerBits.run primitive W (74+2*k)
  let precision := GeneralPaperPowerCeilingBits.run primitive W (max minimum.1.power (64*E*c.nuDen.power))
  let columns := GeneralPaperPowerCeilingBits.run primitive W (G+1)
  (⟨⟨precision.1.power,precision.1.doublings,columns.1.doublings,
    c.nuDen.work+minimum.1.work+precision.1.work+columns.1.work+s.work+t.work+64⟩,G,E⟩,
    minimum.2+precision.2+columns.2+rawWork primitive lambda k t.rows s.meshDenominator c.nuDen.power minimum.1.power+128*W)

theorem data (primitive : ℕ → ℕ) (W lambda k : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (hc : c=GeneralPaperSourceParameterPrice.specification k) (s : GeneralPaperSourceParameters.Parameters)
    (hs : s=GeneralPaperSourceParameters.prepare k) (t : GeneralPaperTrajectoryParameters.Parameters)
    (ht : t=GeneralPaperTrajectoryParameters.prepare lambda k) :
    (fromCache primitive W lambda k c s t).1=specification lambda k := by
  subst c; subst s; subst t
  simp only [fromCache,GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data,
    GeneralPaperSourceParameterPrice.specification,specification,GeneralPaperPowerPrecision.prepare,
    GeneralPaperPowerPrecision.levelBound,GeneralPaperPowerPrecision.errorFactor,level,error]

def profile (primitive : ℕ → ℕ) (W lambda k : ℕ) : ℕ :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let nu := (GeneralPaperScoreScaleParameters.powerRun (32+k)).power
  let minimum := (GeneralPaperScoreScaleParameters.powerRun (74+2*k)).power
  64*(74+2*k+1)*(W+primitive (8+2*(74+2*k)))+
    ceilingProfile primitive W (target lambda t.rows s.meshDenominator nu minimum)+
    ceilingProfile primitive W (level t.rows s.meshDenominator+1)+
    22*primitive (rawWidth lambda k t.rows s.meshDenominator nu minimum)+128*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W lambda k : ℕ)
    (c : GeneralPaperSourceParameterPrice.Cache) (hc : c=GeneralPaperSourceParameterPrice.specification k)
    (s : GeneralPaperSourceParameters.Parameters) (hs : s=GeneralPaperSourceParameters.prepare k)
    (t : GeneralPaperTrajectoryParameters.Parameters) (ht : t=GeneralPaperTrajectoryParameters.prepare lambda k) :
    (fromCache primitive W lambda k c s t).2≤profile primitive W lambda k := by
  subst c; subst s; subst t
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let nu := (GeneralPaperScoreScaleParameters.powerRun (32+k)).power
  let minimum := (GeneralPaperScoreScaleParameters.powerRun (74+2*k)).power
  have hm := GeneralPaperDyadicPowerBits.work primitive hMono W (74+2*k)
  have hp := ceiling_work primitive hMono W (target lambda t.rows s.meshDenominator nu minimum)
  have hc := ceiling_work primitive hMono W (level t.rows s.meshDenominator+1)
  have hr := raw_work primitive hMono lambda k t.rows s.meshDenominator nu minimum
  unfold fromCache profile
  dsimp only
  rw [GeneralPaperDyadicPowerBits.data]
  change (GeneralPaperDyadicPowerBits.run primitive W (74+2*k)).2+
    (GeneralPaperPowerCeilingBits.run primitive W (target lambda t.rows s.meshDenominator nu minimum)).2+
    (GeneralPaperPowerCeilingBits.run primitive W (level t.rows s.meshDenominator+1)).2+
    rawWork primitive lambda k t.rows s.meshDenominator nu minimum+128*W≤_
  dsimp only [s,t,nu,minimum] at *
  omega

end Blotto.GeneralPaperPrecisionParameterPrice
