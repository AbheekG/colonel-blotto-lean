import Blotto.GeneralPaperBasisPreparationStageBits

/-! Unsigned arithmetic operand/result-write prices. Natural subtraction,
multiplication and addition are charged explicitly when computing packed
coordinates; no constant-time bit multiplication is assumed.
-/
namespace Blotto.GeneralPaperNaturalPrimitivePrice
set_option autoImplicit false

def word (a : ℕ) : ℕ := 1+binaryWordWidth a
def binary (primitive : ℕ → ℕ) (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  primitive (max (word a) (word b))+primitive (word (op a b))

theorem binary_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℕ → ℕ → ℕ)
    (a b M : ℕ) (ha : a≤M) (hb : b≤M) (hc : op a b≤M) :
    binary primitive op a b≤2*primitive (1+binaryWordWidth M) := by
  have hi := hMono (max_le (Nat.add_le_add_left (binaryWordWidth_mono ha) 1) (Nat.add_le_add_left (binaryWordWidth_mono hb) 1))
  have ho := hMono (Nat.add_le_add_left (binaryWordWidth_mono hc) 1)
  unfold binary word at *
  omega

end Blotto.GeneralPaperNaturalPrimitivePrice
