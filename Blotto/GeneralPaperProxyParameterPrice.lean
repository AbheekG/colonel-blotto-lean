import Blotto.GeneralPaperQuadraticGridPrice
import Blotto.GeneralPaperProxyParameters

/-! One execution constructs and retains score controls and root controls.
The score depth remains in the returned cache for later callers. All raw
arithmetic outside the child constructors is priced; no native phase is
replayed to obtain its work annotation or a projected parameter.
-/
namespace Blotto.GeneralPaperProxyParameterPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rawWidth (m K d Q : ℕ) : ℕ :=
  32+4*(binaryWordWidth m+binaryWordWidth K+binaryWordWidth d+binaryWordWidth Q)

def rawWork (primitive : ℕ → ℕ) (m K d Q : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) K 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) m (K-1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) m 3+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) d 2+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 Q

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m K d Q : ℕ) :
    rawWork primitive m K d Q≤10*primitive (rawWidth m K d Q) := by
  let L := rawWidth m K d Q
  have hPred := binaryWordWidth_mono (show K-1≤K by omega)
  have hDim := binaryWordWidth_mul m (K-1)
  have hBase := GeneralPaperRayOperandWidthEnvelope.word_add m 3
  have hExp := GeneralPaperRayOperandWidthEnvelope.word_add d 2
  have hCap := binaryWordWidth_mul 2 Q
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h3 : binaryWordWidth 3=2 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) K 1 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) m (K-1) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) m 3 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) d 2 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 Q L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  dsimp only [L] at ha hb hc hd he
  unfold rawWork
  omega

def run (primitive : ℕ → ℕ) (W m k : ℕ) :
    (GeneralPaperScoreScaleParameters.Parameters × GeneralPaperProxyParameters.Parameters) × ℕ :=
  let score := GeneralPaperScoreScalePrice.run primitive W m k
  let dimension := m*(score.1.K-1)
  let determinant := GeneralPaperNatPowerBits.run primitive W (m+3) (dimension+2)
  let grid := GeneralPaperQuadraticGridPrice.run primitive W determinant.1.power
  ((score.1,⟨score.1.K,score.1.S,dimension,determinant.1.power,grid.1.power,grid.1.doublings,2*grid.1.power,
    score.1.work+determinant.1.work+grid.1.work+32⟩),
    score.2+determinant.2+grid.2+rawWork primitive m score.1.K dimension grid.1.power+128*W)

theorem data (primitive : ℕ → ℕ) (W m k : ℕ) :
    (run primitive W m k).1=
      (GeneralPaperScoreScaleParameters.prepare m k,GeneralPaperProxyParameters.prepare m k) := by
  simp only [run,GeneralPaperScoreScalePrice.data,GeneralPaperNatPowerBits.data,
    GeneralPaperQuadraticGridPrice.data,GeneralPaperProxyParameters.prepare]

def profile (primitive : ℕ → ℕ) (W m k : ℕ) : ℕ :=
  let c := GeneralPaperProxyParameters.prepare m k
  GeneralPaperScoreScalePrice.profile primitive W m k+
  64*(binaryWordWidth (c.d+2)+1)*(W+primitive (GeneralPaperNatPowerOperands.width (m+3) (c.d+2)))+
  GeneralPaperQuadraticGridPrice.profile primitive W c.H+
  10*primitive (rawWidth m c.K c.d c.Qg)+128*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k : ℕ) :
    (run primitive W m k).2≤profile primitive W m k := by
  let c := GeneralPaperProxyParameters.prepare m k
  have hs := GeneralPaperScoreScalePrice.work primitive hMono W m k
  have hd := GeneralPaperNatPowerBits.work primitive hMono W (m+3) (c.d+2) (by omega)
  have hg := GeneralPaperQuadraticGridPrice.work primitive hMono W c.H
  have hr := raw_work primitive hMono m c.K c.d c.Qg
  unfold run
  dsimp only
  rw [GeneralPaperScoreScalePrice.data,GeneralPaperNatPowerBits.data,GeneralPaperQuadraticGridPrice.data]
  change (GeneralPaperScoreScalePrice.run primitive W m k).2+
    (GeneralPaperNatPowerBits.run primitive W (m+3) (c.d+2)).2+
    (GeneralPaperQuadraticGridPrice.run primitive W c.H).2+
    rawWork primitive m c.K c.d c.Qg+128*W≤_
  unfold profile
  dsimp only
  dsimp only [c] at *
  omega

theorem unit_work (m k : ℕ) :
    (run (fun _ => 1) 1 m k).2≤
      GeneralPaperScoreScalePrice.profile (fun _ => 1) 1 m k+
      128*(binaryWordWidth ((GeneralPaperProxyParameters.prepare m k).d+2)+1)+
      256*(binaryWordWidth (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H)+1)+138 := by
  have hh := work (fun _ => 1) (by intro a b hab; rfl) 1 m k
  change (run (fun _ => 1) 1 m k).2≤
    GeneralPaperScoreScalePrice.profile (fun _ => 1) 1 m k+
    64*(binaryWordWidth ((GeneralPaperProxyParameters.prepare m k).d+2)+1)*2+
    128*(binaryWordWidth (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H)+1)*2+10+128 at hh
  omega

end Blotto.GeneralPaperProxyParameterPrice
