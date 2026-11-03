import Blotto.GeneralPaperBalancedBitDecoder

/-! Named rational scalar primitives in the paper bit model. Each step
loads its operands, performs its named arithmetic (including the division
zero test), writes its result and prices fixed source control/reference work.
The model's Rat price is the declared exact-rational primitive convention. -/
namespace Blotto.GeneralPaperRationalScalarStep
set_option autoImplicit false

inductive Op where
  | add | sub | mul | div

def Op.apply : Op → ℚ → ℚ → ℚ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

def run (model : RationalCostModel) (A : ℕ) (op : Op) (a b : ℚ) : ℚ × ℕ :=
  let value := op.apply a b
  (value, rationalWordWidth a + rationalWordWidth b + rationalWordWidth value +
    2 * model.rat (max (rationalWordWidth a) (rationalWordWidth b)) + 16 * A + 16)

theorem data (model : RationalCostModel) (A : ℕ) (op : Op) (a b : ℚ) : (run model A op a b).1 = op.apply a b := rfl

theorem work (model : RationalCostModel) (A : ℕ) (op : Op) (a b : ℚ) (s : ℕ)
    (ha : RationalHeight a s) (hb : RationalHeight b s) (ho : RationalHeight (op.apply a b) s) :
    (run model A op a b).2 ≤ 5 * model.rat (1 + 2 * s) + 16 * A + 16 := by
  have h1 := (rationalWordWidth_of_height ha).trans (model.word_le _)
  have h2 := (rationalWordWidth_of_height hb).trans (model.word_le _)
  have h3 := (rationalWordWidth_of_height ho).trans (model.word_le _)
  have h4 := model.monotone (max_le (rationalWordWidth_of_height ha) (rationalWordWidth_of_height hb))
  unfold run
  dsimp only
  omega

def natural (A : ℕ) (n : ℕ) : ℚ × ℕ :=
  ((n : ℚ), binaryWordWidth n + rationalWordWidth (n : ℚ) + 16 * A + 16)

theorem natural_work (model : RationalCostModel) (A n s : ℕ) (hn : RationalHeight (n : ℚ) s)
    (hw : binaryWordWidth n ≤ 1 + 2 * s) :
    (natural A n).2 ≤ 2 * model.rat (1 + 2 * s) + 16 * A + 16 := by
  have h1 := (rationalWordWidth_of_height hn).trans (model.word_le _)
  have h2 := hw.trans (model.word_le _)
  unfold natural
  omega

end Blotto.GeneralPaperRationalScalarStep
