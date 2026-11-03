import Blotto.GeneralPaperFullGridPreparation

/-! Construct both root spans from the retained alphabet scale. The
natural-to-rational cast and both products use their actual operand words.
Their size is linear in lambda, rather than logarithmic in lambda.
-/
namespace Blotto.GeneralPaperSharedSpanPrice
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (a : Alphabet) : ℕ := 64+8*a.lambda

theorem scale_word (a : Alphabet) : binaryWordWidth a.C≤1+2*a.lambda := by
  have hC := binaryWordWidth_mono (show a.C≤8*a.C by omega)
  rw [a.dyadic] at hC
  have hp := GeneralPaperNatPowerOperands.power_width 2 a.lambda
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  omega

theorem widths (a : Alphabet) :
    rationalWordWidth (a.C:ℚ)≤width a ∧ rationalWordWidth (8:ℚ)≤width a ∧
      rationalWordWidth ((8:ℚ)*a.C)≤width a ∧ rationalWordWidth (2:ℚ)≤width a ∧
      rationalWordWidth ((2:ℚ)*(8*a.C))≤width a := by
  have hC := (GeneralPaperBasisDivideBits.nat_height a.C).mono (scale_word a)
  have h8 := GeneralPaperBasisDivideBits.nat_height 8
  have h2 := GeneralPaperBasisDivideBits.nat_height 2
  change RationalHeight (8:ℚ) 4 at h8
  change RationalHeight (2:ℚ) 2 at h2
  have hU := h8.mul hC
  have hS := h2.mul hU
  have hc := rationalWordWidth_of_height hC
  have hEight := rationalWordWidth_of_height h8
  have hu := rationalWordWidth_of_height hU
  have hTwo := rationalWordWidth_of_height h2
  have hs := rationalWordWidth_of_height hS
  unfold width
  omega

def run (primitive : ℕ → ℕ) (W : ℕ) (a : Alphabet) : (ℚ × ℚ) × ℕ :=
  let scale : ℚ := a.C
  let unsigned := 8*scale
  let signed := 2*unsigned
  ((unsigned,signed),primitive (rationalWordWidth scale)+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x*y) 8 scale+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x*y) 2 unsigned+64*W)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (a : Alphabet) :
    (run primitive W a).1=((8:ℚ)*a.C,(2:ℚ)*(8*a.C)) := rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ) (a : Alphabet) :
    (run primitive W a).2≤5*primitive (width a)+64*W := by
  have hs := widths a
  have hCast := hMono hs.1
  have hUnsigned := GeneralPaperRationalPrimitivePrice.binary_le primitive hMono (fun x y => x*y)
    8 (a.C:ℚ) (width a) hs.2.1 hs.1 hs.2.2.1
  have hSigned := GeneralPaperRationalPrimitivePrice.binary_le primitive hMono (fun x y => x*y)
    2 ((8:ℚ)*a.C) (width a) hs.2.2.2.1 hs.2.2.1 hs.2.2.2.2
  change primitive (rationalWordWidth (a.C:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x*y) 8 (a.C:ℚ)+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x*y) 2 ((8:ℚ)*a.C)+64*W≤_
  omega

theorem arithmetic_work (a : Alphabet) : (run (fun _ => 1) 1 a).2=69 := rfl

end Blotto.GeneralPaperSharedSpanPrice
