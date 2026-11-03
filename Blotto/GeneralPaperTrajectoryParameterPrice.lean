import Blotto.GeneralPaperParameterOperandBounds

/-! Build trajectory controls from the retained source period. The period
constructor is not replayed; its native annotation is read from the cache.
The new factor, epoch ceiling, row product and all raw arithmetic are priced.
-/
namespace Blotto.GeneralPaperTrajectoryParameterPrice
set_option autoImplicit false
set_option maxHeartbeats 8000000

def rawWidth (lambda k period factor epochs depth periodDepth : ℕ) : ℕ :=
  64+8*(binaryWordWidth lambda+binaryWordWidth k+binaryWordWidth period+binaryWordWidth factor+
    binaryWordWidth epochs+binaryWordWidth depth+binaryWordWidth periodDepth)

def rawWork (primitive : ℕ → ℕ) (lambda k period factor epochs depth periodDepth : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 35 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) lambda 2+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (lambda+2) factor+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) epochs period+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) depth periodDepth

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (lambda k period factor epochs depth periodDepth : ℕ) :
    rawWork primitive lambda k period factor epochs depth periodDepth≤
      10*primitive (rawWidth lambda k period factor epochs depth periodDepth) := by
  let L := rawWidth lambda k period factor epochs depth periodDepth
  have he := GeneralPaperRayOperandWidthEnvelope.word_add 35 k
  have hl := GeneralPaperRayOperandWidthEnvelope.word_add lambda 2
  have ht := binaryWordWidth_mul (lambda+2) factor
  have hr := binaryWordWidth_mul epochs period
  have hd := GeneralPaperRayOperandWidthEnvelope.word_add depth periodDepth
  have h2 : binaryWordWidth 2=2 := by decide
  have h35 : binaryWordWidth 35=6 := by decide
  have hA := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 35 k L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hB := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) lambda 2 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hC := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (lambda+2) factor L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hD := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) epochs period L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hE := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) depth periodDepth L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  change _≤10*primitive L
  unfold rawWork
  omega

def fromCache (primitive : ℕ → ℕ) (W lambda k : ℕ) (c : GeneralPaperSourceParameterPrice.Cache) :
    GeneralPaperTrajectoryParameters.Parameters × ℕ :=
  let factor := GeneralPaperDyadicPowerBits.run primitive W (35+k)
  let epochs := GeneralPaperPowerCeilingBits.run primitive W ((lambda+2)*factor.1.power)
  (⟨c.zDen.power,epochs.1.power,epochs.1.power*c.zDen.power,epochs.1.doublings+c.zDen.doublings,
    c.zDen.work+factor.1.work+epochs.1.work+24⟩,
    factor.2+epochs.2+rawWork primitive lambda k c.zDen.power factor.1.power epochs.1.power epochs.1.doublings c.zDen.doublings+128*W)

theorem data (primitive : ℕ → ℕ) (W lambda k : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (hc : c=GeneralPaperSourceParameterPrice.specification k) :
    (fromCache primitive W lambda k c).1=GeneralPaperTrajectoryParameters.prepare lambda k := by
  subst c
  simp only [fromCache,GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data,
    GeneralPaperSourceParameterPrice.specification,GeneralPaperTrajectoryParameters.prepare]

def target (lambda k : ℕ) : ℕ := (lambda+2)*(GeneralPaperScoreScaleParameters.powerRun (35+k)).power

def profile (primitive : ℕ → ℕ) (W lambda k : ℕ) : ℕ :=
  let p := GeneralPaperScoreScaleParameters.powerRun (11+k)
  let f := GeneralPaperScoreScaleParameters.powerRun (35+k)
  let e := GeneralPaperPowerCeiling.ceiling (target lambda k)
  64*(35+k+1)*(W+primitive (8+2*(35+k)))+
    64*(binaryWordWidth (target lambda k)+1)*(W+primitive (1+binaryWordWidth (2*(target lambda k+1))))+
    10*primitive (rawWidth lambda k p.power f.power e.power e.doublings p.doublings)+128*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W lambda k : ℕ)
    (c : GeneralPaperSourceParameterPrice.Cache) (hc : c=GeneralPaperSourceParameterPrice.specification k) :
    (fromCache primitive W lambda k c).2≤profile primitive W lambda k := by
  subst c
  let p := GeneralPaperScoreScaleParameters.powerRun (11+k)
  let f := GeneralPaperScoreScaleParameters.powerRun (35+k)
  let e := GeneralPaperPowerCeiling.ceiling (target lambda k)
  have hf := GeneralPaperDyadicPowerBits.work primitive hMono W (35+k)
  have he := GeneralPaperPowerCeilingBits.work primitive hMono W (target lambda k)
  have hr := raw_work primitive hMono lambda k p.power f.power e.power e.doublings p.doublings
  unfold fromCache profile
  dsimp only
  rw [GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data]
  change _≤64*(35+k+1)*(W+primitive (8+2*(35+k)))+
    64*(binaryWordWidth (target lambda k)+1)*(W+primitive (1+binaryWordWidth (2*(target lambda k+1))))+
    10*primitive (rawWidth lambda k p.power f.power e.power e.doublings p.doublings)+128*W
  change (GeneralPaperDyadicPowerBits.run primitive W (35+k)).2+
    (GeneralPaperPowerCeilingBits.run primitive W (target lambda k)).2+
    rawWork primitive lambda k p.power f.power e.power e.doublings p.doublings+128*W≤_
  omega

theorem both_data (primitive : ℕ → ℕ) (W lambda k : ℕ) (c : GeneralPaperSourceParameterPrice.Cache)
    (hc : c=GeneralPaperSourceParameterPrice.specification k) :
    (fromCache primitive W lambda k c).1=(fromCache (fun _ => 1) 1 lambda k c).1 := by rw [data _ _ _ _ _ hc,data _ _ _ _ _ hc]

end Blotto.GeneralPaperTrajectoryParameterPrice
