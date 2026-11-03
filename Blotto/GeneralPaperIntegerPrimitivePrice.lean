import Blotto.GeneralPaperSharedBasisWork

/-! Signed integer operand/result-write prices in the declared paper
arithmetic model. A monotone primitive can be unit price or the paper's
fast arithmetic price; the actual operation and every written result are
charged, including unreduced products and integer exact-division operands.
-/
namespace Blotto.GeneralPaperIntegerPrimitivePrice
set_option autoImplicit false

def word (a : ℤ) : ℕ := 1+binaryWordWidth a.natAbs

def binary (primitive : ℕ → ℕ) (op : ℤ → ℤ → ℤ) (a b : ℤ) : ℕ :=
  primitive (max (word a) (word b))+primitive (word (op a b))

def unary (primitive : ℕ → ℕ) (op : ℤ → ℤ) (a : ℤ) : ℕ :=
  primitive (word a)+primitive (word (op a))

theorem word_bound (a : ℤ) (M : ℕ) (ha : a.natAbs≤M) : word a≤1+binaryWordWidth M :=
  Nat.add_le_add_left (binaryWordWidth_mono ha) 1

theorem binary_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℤ → ℤ → ℤ)
    (a b : ℤ) (M : ℕ) (ha : a.natAbs≤M) (hb : b.natAbs≤M) (hc : (op a b).natAbs≤M) :
    binary primitive op a b≤2*primitive (1+binaryWordWidth M) := by
  have hi := hMono (max_le (word_bound a M ha) (word_bound b M hb))
  have ho := hMono (word_bound (op a b) M hc)
  unfold binary
  omega

theorem unary_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℤ → ℤ)
    (a : ℤ) (M : ℕ) (ha : a.natAbs≤M) (hb : (op a).natAbs≤M) :
    unary primitive op a≤2*primitive (1+binaryWordWidth M) := by
  have hi := hMono (word_bound a M ha)
  have ho := hMono (word_bound (op a) M hb)
  unfold unary
  omega

end Blotto.GeneralPaperIntegerPrimitivePrice
