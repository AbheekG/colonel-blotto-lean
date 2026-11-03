import Blotto.GeneralPaperBasisAdvanceBits

/-! Construct the actual ray budget betaN/N once per native stage.
Both integer-to-rational writes and the division are priced explicitly.
-/
namespace Blotto.GeneralPaperBasisBudgetBits
open GeneralPaperRationalPrimitivePrice
set_option autoImplicit false

def width (N B : ℕ) : ℕ := 1+2*(binaryWordWidth N+binaryWordWidth B)

def run (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) : ℚ × ℕ :=
  ((betaN:ℚ)/(N:ℚ),24*W+primitive (rationalWordWidth (betaN:ℚ))+primitive (rationalWordWidth (N:ℚ))+
    binary primitive (fun a b => a/b) (betaN:ℚ) (N:ℚ))

theorem data (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) : (run primitive W N betaN).1=(betaN:ℚ)/(N:ℚ) := rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N B : ℕ) (betaN : ℤ) (hB : betaN.natAbs≤B) :
    (run primitive W N betaN).2≤24*W+4*primitive (width N B) := by
  have hb := GeneralPaperBasisStageSize.int_height betaN B hB
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hv := hb.div hn
  have hBeta : rationalWordWidth (betaN:ℚ)≤width N B := (rationalWordWidth_of_height hb).trans (by unfold width; omega)
  have hN : rationalWordWidth (N:ℚ)≤width N B := (rationalWordWidth_of_height hn).trans (by unfold width; omega)
  have hV : rationalWordWidth ((betaN:ℚ)/(N:ℚ))≤width N B := (rationalWordWidth_of_height hv).trans (by unfold width; omega)
  have h1 := hMono hBeta
  have h2 := hMono hN
  have hd := binary_le primitive hMono (fun a b => a/b) _ _ _ hBeta hN hV
  dsimp only [run]
  omega

end Blotto.GeneralPaperBasisBudgetBits
