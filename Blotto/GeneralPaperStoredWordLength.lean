import Blotto.GeneralPaperEqualClosedPreparation

/-! Integer word-length extraction in the paper bit model. Its primitive
scans the stored integer word and writes its scalar length. The price includes
both words, control and references; no supplied length is used by the program. -/
namespace Blotto.GeneralPaperStoredWordLength
set_option autoImplicit false

def run (A n : ℕ) : ℕ × ℕ :=
  let length := binaryWordWidth n
  (length, 32 * (length + binaryWordWidth length + A + 1))

theorem data (A n : ℕ) : (run A n).1 = binaryWordWidth n := rfl

theorem work (A n : ℕ) : (run A n).2 ≤ 64 * (binaryWordWidth n + A + 1) := by
  have h : binaryWordWidth (binaryWordWidth n) ≤ binaryWordWidth n + 1 :=
    Nat.add_le_add_right (Nat.log2_le_self (binaryWordWidth n)) 1
  change 32 * (binaryWordWidth n + binaryWordWidth (binaryWordWidth n) + A + 1) ≤
    64 * (binaryWordWidth n + A + 1)
  omega

end Blotto.GeneralPaperStoredWordLength
