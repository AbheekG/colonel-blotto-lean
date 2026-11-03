import Blotto.GeneralPaperProxyParameterPrice

/-! Construct the bid alphabet's Kc,J,D,C,Lambda from the retained proxy
denominator cap. Labels, determinant power and scale are each executed once.
Every literal operand/result outside those constructors is also charged.
-/
namespace Blotto.GeneralPaperComparatorParameterPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rawWidth (m k K qbar power : ℕ) : ℕ :=
  64+4*(binaryWordWidth m+binaryWordWidth k+binaryWordWidth K+binaryWordWidth qbar+binaryWordWidth power)

def rawWork (primitive : ℕ → ℕ) (m k K qbar power : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 17 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) K 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) m (K-1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (m*(K-1)) 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) m 2+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) qbar power

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m k K qbar power : ℕ) :
    rawWork primitive m k K qbar power≤12*primitive (rawWidth m k K qbar power) := by
  let L := rawWidth m k K qbar power
  have hPred := binaryWordWidth_mono (show K-1≤K by omega)
  have hDim := binaryWordWidth_mul m (K-1)
  have hJ := GeneralPaperRayOperandWidthEnvelope.word_add (m*(K-1)) 1
  have hBase := GeneralPaperRayOperandWidthEnvelope.word_add m 2
  have hExp := GeneralPaperRayOperandWidthEnvelope.word_add 17 k
  have hDen := binaryWordWidth_mul qbar power
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h17 : binaryWordWidth 17=5 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 17 k L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) K 1 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) m (K-1) L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (m*(K-1)) 1 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) m 2 L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  have hf := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) qbar power L
    (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega) (by dsimp [L,rawWidth]; omega)
  dsimp only [L] at ha hb hc hd he hf
  unfold rawWork
  omega

def run (primitive : ℕ → ℕ) (W m k qbar : ℕ) : GeneralPaperComparatorParameters.Parameters × ℕ :=
  let labels := GeneralPaperDyadicPowerBits.run primitive W (17+k)
  let dimension := m*(labels.1.power-1)+1
  let determinant := GeneralPaperNatPowerBits.run primitive W (m+2) dimension
  let denominator := qbar*determinant.1.power
  let scale := GeneralPaperQuadraticGridPrice.run primitive W denominator
  (⟨labels.1.power,dimension,denominator,scale.1.power,scale.1.doublings+3,
    labels.1.work+determinant.1.work+scale.1.work+32⟩,
    labels.2+determinant.2+scale.2+rawWork primitive m k labels.1.power qbar determinant.1.power+128*W)

theorem data (primitive : ℕ → ℕ) (W m k qbar : ℕ) :
    (run primitive W m k qbar).1=GeneralPaperComparatorParameters.prepare m k qbar := by
  simp only [run,GeneralPaperDyadicPowerBits.data,GeneralPaperNatPowerBits.data,
    GeneralPaperQuadraticGridPrice.data,GeneralPaperComparatorParameters.prepare,GeneralPaperComparatorParameters.countRun]

def profile (primitive : ℕ → ℕ) (W m k qbar : ℕ) : ℕ :=
  let c := GeneralPaperComparatorParameters.prepare m k qbar
  64*((17+k)+1)*(W+primitive (8+2*(17+k)))+
  64*(binaryWordWidth c.J+1)*(W+primitive (GeneralPaperNatPowerOperands.width (m+2) c.J))+
  GeneralPaperQuadraticGridPrice.profile primitive W c.D+
  12*primitive (rawWidth m k c.Kc qbar ((m+2)^c.J))+128*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k qbar : ℕ) :
    (run primitive W m k qbar).2≤profile primitive W m k qbar := by
  let c := GeneralPaperComparatorParameters.prepare m k qbar
  have hl := GeneralPaperDyadicPowerBits.work primitive hMono W (17+k)
  have hd := GeneralPaperNatPowerBits.work primitive hMono W (m+2) c.J (by omega)
  have hs := GeneralPaperQuadraticGridPrice.work primitive hMono W c.D
  have hr := raw_work primitive hMono m k c.Kc qbar ((m+2)^c.J)
  unfold run
  dsimp only
  rw [GeneralPaperDyadicPowerBits.data,GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data _ _).1]
  change (GeneralPaperDyadicPowerBits.run primitive W (17+k)).2+
    (GeneralPaperNatPowerBits.run primitive W (m+2) c.J).2+
    (GeneralPaperQuadraticGridPrice.run primitive W (qbar*(m+2)^c.J)).2+
    rawWork primitive m k c.Kc qbar ((m+2)^c.J)+128*W≤_
  have hD : c.D=qbar*(m+2)^c.J := (GeneralPaperComparatorParameters.data m k qbar).2.2.1
  rw [hD] at hs
  unfold profile
  dsimp only
  change _≤64*((17+k)+1)*(W+primitive (8+2*(17+k)))+
    64*(binaryWordWidth c.J+1)*(W+primitive (GeneralPaperNatPowerOperands.width (m+2) c.J))+
    GeneralPaperQuadraticGridPrice.profile primitive W c.D+
    12*primitive (rawWidth m k c.Kc qbar ((m+2)^c.J))+128*W
  rw [hD]
  dsimp only [c] at *
  omega

end Blotto.GeneralPaperComparatorParameterPrice
