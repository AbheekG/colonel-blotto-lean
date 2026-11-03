import Blotto.GeneralPaperInitializedBasisWork

/-! Operand-width forms of the unsigned/signed primitive prices. They
bound the literal input and written output words, including intermediate
products before reduction, without an externally supplied magnitude oracle.
-/
namespace Blotto.GeneralPaperIntegerWordPrice
set_option autoImplicit false

def compare (primitive : ℕ → ℕ) (a b : ℕ) : ℕ :=
  primitive (max (GeneralPaperNaturalPrimitivePrice.word a) (GeneralPaperNaturalPrimitivePrice.word b))

theorem compare_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (a b L : ℕ)
    (ha : 1+binaryWordWidth a≤L) (hb : 1+binaryWordWidth b≤L) : compare primitive a b≤primitive L :=
  hMono (max_le ha hb)

theorem natural_binary (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℕ → ℕ → ℕ) (a b L : ℕ)
    (ha : 1+binaryWordWidth a≤L) (hb : 1+binaryWordWidth b≤L) (hc : 1+binaryWordWidth (op a b)≤L) :
    GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L := by
  have hi := hMono (max_le ha hb)
  have ho := hMono hc
  unfold GeneralPaperNaturalPrimitivePrice.binary GeneralPaperNaturalPrimitivePrice.word
  omega

theorem integer_binary (primitive : ℕ → ℕ) (hMono : Monotone primitive) (op : ℤ → ℤ → ℤ) (a b : ℤ) (L : ℕ)
    (ha : GeneralPaperIntegerPrimitivePrice.word a≤L) (hb : GeneralPaperIntegerPrimitivePrice.word b≤L)
    (hc : GeneralPaperIntegerPrimitivePrice.word (op a b)≤L) :
    GeneralPaperIntegerPrimitivePrice.binary primitive op a b≤2*primitive L := by
  have hi := hMono (max_le ha hb)
  have ho := hMono hc
  unfold GeneralPaperIntegerPrimitivePrice.binary
  omega

end Blotto.GeneralPaperIntegerWordPrice
