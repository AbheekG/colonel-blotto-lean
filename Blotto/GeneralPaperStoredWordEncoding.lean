import Blotto.GeneralPaperStoredRejectionWidth

/-! Fused fixed-width encoding from an actual stored natural and width.
Each reached quotient, remainder and Boolean/list cell is computed once.
All wide operand/result copies, arithmetic and control are priced. -/
namespace Blotto.GeneralPaperStoredWordEncoding
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run (model : RationalCostModel) (A : ℕ) : ℕ → ℕ → List Bool × ℕ
  | 0, _ => ([], 64 * A + 64)
  | length + 1, n =>
    let quotient := n / 2
    let digit := n % 2
    let bit := decide (digit = 1)
    let child := run model A length quotient
    (bit :: child.1, child.2 + binaryWordWidth n + binaryWordWidth quotient + binaryWordWidth digit +
      4 * model.rat (binaryWordWidth n + 3) + 64 * (A + binaryWordWidth (length + 2) + 1))

theorem data (model : RationalCostModel) (A length n : ℕ) :
    (run model A length n).1 = BinaryPayload.bits length n := by
  induction length generalizing n with
  | zero => simp [run, BinaryPayload.bits]
  | succ length ih =>
    rw [run]
    dsimp only
    rw [ih]
    simp only [BinaryPayload.bits, List.ofFn_succ]
    change (decide (n % 2 = 1) :: List.ofFn (fun j : Fin length => (n / 2).testBit j.val)) =
      n.testBit 0 :: List.ofFn (fun i : Fin length => n.testBit (i.val + 1))
    simp only [Nat.testBit_zero, Nat.testBit_add_one]

def word (model : RationalCostModel) (A length n : ℕ) : FixedBinaryWord length × ℕ :=
  let actual := run model A length n
  (⟨actual.1, (by rw [data]; exact BinaryPayload.bits_length length n)⟩, actual.2)

theorem word_data (model : RationalCostModel) (A length n : ℕ) :
    (word model A length n).1 = FixedBinaryWord.ofNat length n := by
  simp only [word, data, FixedBinaryWord.ofNat]

def stepBound (model : RationalCostModel) (A width L : ℕ) : ℕ :=
  8 * model.rat (L + 4) + 128 * (A + binaryWordWidth (width + 1) + 1)

theorem bounded_work (model : RationalCostModel) (A width L length : ℕ) (hl : length ≤ width)
    (n : ℕ) (hn : binaryWordWidth n ≤ L) :
    (run model A length n).2 ≤ length * stepBound model A width L + 64 * A + 64 := by
  induction length generalizing n with
  | zero => simp only [run, zero_mul, zero_add, le_refl]
  | succ length ih =>
    have hQ := binaryWordWidth_mono (Nat.div_le_self n 2)
    have hDigit : binaryWordWidth (n % 2) ≤ 1 := by
      have h := binaryWordWidth_mono (show n % 2 ≤ 1 by omega)
      have h1 : binaryWordWidth 1 = 1 := by decide
      omega
    have hI := binaryWordWidth_mono (show length + 2 ≤ width + 1 by omega)
    have hChild := ih (by omega) (n / 2) (by omega)
    have hRat := model.monotone (show binaryWordWidth n + 3 ≤ L + 4 by omega)
    have hWord := model.word_le (L + 4)
    rw [run]
    dsimp only
    unfold stepBound at hChild ⊢
    nlinarith only [hQ, hn, hDigit, hI, hChild, hRat, hWord]

theorem work (model : RationalCostModel) (A width n L : ℕ) (hn : binaryWordWidth n ≤ L) :
    (word model A width n).2 ≤ width * stepBound model A width L + 64 * A + 64 :=
  bounded_work model A width L width le_rfl n hn

end Blotto.GeneralPaperStoredWordEncoding
