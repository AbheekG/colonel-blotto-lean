import Blotto.GeneralPaperPowerTablePrice

/-! Construct the stored geometric base from already retained precision.
The dyadic decrement, all index/mantissa arithmetic, signed exponent and
native metadata writes are priced. The precision constructor is not called.
-/
namespace Blotto.GeneralPaperStoredBasePrice
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def rawWidth (unit p k : ℕ) (q : GeneralPaperPowerCeiling.Result) : ℕ :=
  128+16*(binaryWordWidth unit+binaryWordWidth p+binaryWordWidth k+binaryWordWidth q.power+binaryWordWidth q.work)

def rawWork (primitive : ℕ → ℕ) (unit p k : ℕ) (q : GeneralPaperPowerCeiling.Result) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 55 (2*k)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) p 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) (p+1) (55+2*k)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 unit+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) (2*unit) q.power+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) q.work 16+
  primitive (GeneralPaperIntegerPrimitivePrice.word (p+1:ℕ))+
  GeneralPaperIntegerPrimitivePrice.unary primitive (fun a => -a) (p+1:ℕ)

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (unit p k : ℕ) (q : GeneralPaperPowerCeiling.Result) :
    rawWork primitive unit p k q≤17*primitive (rawWidth unit p k q) := by
  let L := rawWidth unit p k q
  have h2k := binaryWordWidth_mul 2 k
  have h55 := GeneralPaperRayOperandWidthEnvelope.word_add 55 (2*k)
  have hp := GeneralPaperRayOperandWidthEnvelope.word_add p 1
  have hs := binaryWordWidth_mono (show p+1-(55+2*k)≤p+1 by omega)
  have hu := binaryWordWidth_mul 2 unit
  have hm := binaryWordWidth_mono (show 2*unit-q.power≤2*unit by omega)
  have hw := GeneralPaperRayOperandWidthEnvelope.word_add q.work 16
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have hFiftyFive : binaryWordWidth 55=6 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 k L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 55 (2*k) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) p 1 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) (p+1) (55+2*k) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 unit L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hf := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) (2*unit) q.power L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hg := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) q.work 16 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hCast : GeneralPaperIntegerPrimitivePrice.word (p+1:ℕ)≤L := by
    simp only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_natCast]
    dsimp [L,rawWidth]
    omega
  have hNeg : GeneralPaperIntegerPrimitivePrice.word (-(p+1:ℕ):ℤ)≤L := by
    simpa only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_neg] using hCast
  have hh := hMono hCast
  have hi : GeneralPaperIntegerPrimitivePrice.unary primitive (fun a => -a) (p+1:ℕ)≤2*primitive L := by
    have hh' := hMono hNeg
    unfold GeneralPaperIntegerPrimitivePrice.unary
    change primitive (GeneralPaperIntegerPrimitivePrice.word (p+1:ℕ))+
      primitive (GeneralPaperIntegerPrimitivePrice.word (-((p+1:ℕ):ℤ)))≤2*primitive L
    omega
  change _≤17*primitive L
  unfold rawWork
  omega

def run (primitive : ℕ → ℕ) (W unit p k : ℕ) : GeneralPaperDyadicMultiply.Result × ℕ :=
  let q := GeneralPaperDyadicPowerBits.run primitive W (p+1-GeneralPaperStoredGeometricBase.decrementBits k)
  (⟨⟨2*unit-q.1.power,-((p+1:ℕ):ℤ)⟩,q.1.work+16⟩,
    q.2+rawWork primitive unit p k q.1+96*W)

theorem data (primitive : ℕ → ℕ) (W unit p k : ℕ) :
    (run primitive W unit p k).1=GeneralPaperStoredGeometricBase.construct unit p k := by
  simp only [run,GeneralPaperDyadicPowerBits.data,GeneralPaperStoredGeometricBase.construct]

def profile (primitive : ℕ → ℕ) (W unit p k : ℕ) : ℕ :=
  let e := p+1-GeneralPaperStoredGeometricBase.decrementBits k
  64*(e+1)*(W+primitive (8+2*e))+17*primitive (rawWidth unit p k (powerRun e))+96*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p k : ℕ) :
    (run primitive W unit p k).2≤profile primitive W unit p k := by
  let e := p+1-GeneralPaperStoredGeometricBase.decrementBits k
  have hq := GeneralPaperDyadicPowerBits.work primitive hMono W e
  have hr := raw_work primitive hMono unit p k (powerRun e)
  unfold run profile
  dsimp only
  rw [GeneralPaperDyadicPowerBits.data]
  change (GeneralPaperDyadicPowerBits.run primitive W e).2+rawWork primitive unit p k (powerRun e)+96*W≤_
  dsimp only [e] at *
  omega

theorem arithmetic_work (unit p k : ℕ) : (run (fun _ => 1) 1 unit p k).2≤512*(p+2) := by
  have h := work (fun _ => 1) (by intro a b hab; rfl) 1 unit p k
  have he : p+1-GeneralPaperStoredGeometricBase.decrementBits k≤p+1 := by omega
  exact h.trans (by
    change 64*(p+1-GeneralPaperStoredGeometricBase.decrementBits k+1)*2+17+96≤512*(p+2)
    omega)

end Blotto.GeneralPaperStoredBasePrice
