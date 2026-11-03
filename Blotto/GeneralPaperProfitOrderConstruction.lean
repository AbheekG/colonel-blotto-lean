import Blotto.GeneralPaperProfitScalePrice

/-! Materialize the denominator, generated points and ordered grid once.
The endpoint shares the constructed denominator. All constructor work is
charged, including raw denominator/endpoint products.
-/
namespace Blotto.GeneralPaperProfitOrderConstruction
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rawWork (primitive : ℕ → ℕ) (w factor : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) factor w+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 (factor*w)

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (w B : ℕ) :
    rawWork primitive w (2^B)≤4*primitive (GeneralPaperProfitPointPrice.width w B) := by
  have hp := GeneralPaperNatPowerOperands.power_width 2 B
  have hw := binaryWordWidth_mono (show w≤w+1 by omega)
  have hd := binaryWordWidth_mul (2^B) w
  have he := binaryWordWidth_mul 2 (2^B*w)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp he
  have hD := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b)
    (2^B) w (GeneralPaperProfitPointPrice.width w B)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
  have hE := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b)
    2 (2^B*w) (GeneralPaperProfitPointPrice.width w B)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
    (by unfold GeneralPaperProfitPointPrice.width; omega)
  unfold rawWork
  omega

def run (primitive : ℕ → ℕ) (W w B : ℕ) : (List ℕ × ℕ) × ℕ :=
  let dyadic := GeneralPaperDyadicPowerBits.run primitive W B
  let denominator := dyadic.1.power*w
  let generated := GeneralPaperProfitPointPrice.run primitive W w B
  let ordered := GeneralPaperNaturalOrderPrice.run primitive W (2*denominator) generated.1
  ((ordered.1,denominator),dyadic.2+generated.2+ordered.2+rawWork primitive w dyadic.1.power+64*W)

theorem data (primitive : ℕ → ℕ) (W w B : ℕ) :
    (run primitive W w B).1=(GeneralPaperProfitGridPrepare.ordered w B,denominator w B) := by
  simp only [run,GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data B).1,
    GeneralPaperProfitPointPrice.data,GeneralPaperNaturalOrderPrice.data,denominator,
    GeneralPaperProfitGridPrepare.ordered]

def profile (primitive : ℕ → ℕ) (W w B : ℕ) : ℕ :=
  64*(B+1)*(W+primitive (GeneralPaperProfitPointPrice.width w B))+
    GeneralPaperProfitPointPrice.profile primitive W w B+
    GeneralPaperNaturalOrderPrice.profile ((B+1)*w) W (primitive (1+binaryWordWidth (2*denominator w B)))+
    4*primitive (GeneralPaperProfitPointPrice.width w B)+64*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W w B : ℕ) :
    (run primitive W w B).2≤profile primitive W w B := by
  have hPower := GeneralPaperDyadicPowerBits.work primitive hMono W B
  have hWidth : 8+2*B≤GeneralPaperProfitPointPrice.width w B := by unfold GeneralPaperProfitPointPrice.width; omega
  have hP := Nat.mul_le_mul_left (64*(B+1)) (Nat.add_le_add_left (hMono hWidth) W)
  have hPoints := GeneralPaperProfitPointPrice.work primitive hMono W w B
  have hOrder := GeneralPaperProfitOrderPrice.work primitive hMono W w B
  have hRaw := raw_work primitive hMono w B
  change (GeneralPaperDyadicPowerBits.run primitive W B).2+(GeneralPaperProfitPointPrice.run primitive W w B).2+
    (GeneralPaperNaturalOrderPrice.run primitive W (2*((GeneralPaperDyadicPowerBits.run primitive W B).1.power*w))
      (GeneralPaperProfitPointPrice.run primitive W w B).1).2+
    rawWork primitive w (GeneralPaperDyadicPowerBits.run primitive W B).1.power+64*W≤_
  rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data B).1,GeneralPaperProfitPointPrice.data]
  unfold profile
  change _+(GeneralPaperProfitPointPrice.run primitive W w B).2+
    (GeneralPaperNaturalOrderPrice.run primitive W (2*denominator w B) (points w B)).2+rawWork primitive w (2^B)+64*W≤_
  omega

end Blotto.GeneralPaperProfitOrderConstruction
