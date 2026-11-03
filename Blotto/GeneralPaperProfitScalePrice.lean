import Blotto.GeneralPaperControlArrayPrice

/-! Construct the scaled profit-grid array once. Every multiplication and
reference load/write is charged; native scaled-work metadata is separate.
-/
namespace Blotto.GeneralPaperProfitScalePrice
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 6000000

def width (q w B : ℕ) : ℕ := 64+8*(binaryWordWidth q+B+binaryWordWidth (w+1)+1)

theorem multiply_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (q w B value : ℕ)
    (hValue : value≤2*denominator w B) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q value≤2*primitive (width q w B) := by
  have hp := GeneralPaperNatPowerOperands.power_width 2 B
  have hw := binaryWordWidth_mono (show w≤w+1 by omega)
  have hd := binaryWordWidth_mul (2^B) w
  have h2d := binaryWordWidth_mul 2 (denominator w B)
  have hv := binaryWordWidth_mono hValue
  have hm := binaryWordWidth_mul q value
  have h2 : binaryWordWidth 2=2 := by decide
  change binaryWordWidth (denominator w B)≤_ at hd
  rw [h2] at hp h2d
  apply GeneralPaperIntegerWordPrice.natural_binary primitive hMono
  all_goals unfold width; omega

def run {n : ℕ} (index primitive : ℕ → ℕ) (W q : ℕ) (values : FixedArrayTable n ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index W (fun r =>
    (q*values.read r,GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q (values.read r)+16*W))

theorem data {n : ℕ} (index primitive : ℕ → ℕ) (W q : ℕ) (values : FixedArrayTable n ℕ) :
    (run index primitive W q values).1=(GeneralPaperProfitGridPrepare.scaled q values).1 := by
  simp only [run,GeneralPaperProfitGridPrepare.scaled,PaperIndexedArrayConstruction.run_data]

theorem work {n : ℕ} (index primitive : ℕ → ℕ) (hMono : Monotone primitive) (W q w B : ℕ)
    (values : FixedArrayTable n ℕ) (hValues : ∀ i,values.read i≤2*denominator w B)
    (hW : 1≤W) (hIndex : ∀ i≤n,index (binaryWordWidth (i+1))≤W) :
    (run index primitive W q values).2≤n*(2*primitive (width q w B)+16*W)+44*(n+1)*W := by
  apply GeneralPaperControlArrayPrice.indexed_work index W (2*primitive (width q w B)+16*W) _ hW hIndex
  intro i
  exact Nat.add_le_add_right (multiply_work primitive hMono q w B (values.read i) (hValues i)) _

end Blotto.GeneralPaperProfitScalePrice
