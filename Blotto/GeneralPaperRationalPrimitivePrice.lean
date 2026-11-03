import Blotto.GeneralPaperRayBitRefinement

/-! Operand-sensitive prices for a rational result and its write. Unit
primitive prices give the arithmetic model; Rat prices also dominate output
word copying in the bit model. These are declared paper-model prices.
-/
namespace Blotto.GeneralPaperRationalPrimitivePrice
set_option autoImplicit false

def binary (primitive : ℕ → ℕ) (op : ℚ → ℚ → ℚ) (a b : ℚ) : ℕ :=
  primitive (RationalExpression.pairWidth a b)+primitive (rationalWordWidth (op a b))

def unary (primitive : ℕ → ℕ) (op : ℚ → ℚ) (a : ℚ) : ℕ :=
  primitive (rationalWordWidth a)+primitive (rationalWordWidth (op a))

theorem binary_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℚ → ℚ → ℚ)
    (a b : ℚ) (H : ℕ) (ha : rationalWordWidth a≤H) (hb : rationalWordWidth b≤H)
    (hc : rationalWordWidth (op a b)≤H) : binary primitive op a b≤2*primitive H := by
  have hi := hMono (max_le ha hb)
  have ho := hMono hc
  unfold binary RationalExpression.pairWidth at *
  omega

theorem unary_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℚ → ℚ)
    (a : ℚ) (H : ℕ) (ha : rationalWordWidth a≤H) (hb : rationalWordWidth (op a)≤H) :
    unary primitive op a≤2*primitive H := by
  have hi := hMono ha
  have ho := hMono hb
  unfold unary
  omega

end Blotto.GeneralPaperRationalPrimitivePrice
