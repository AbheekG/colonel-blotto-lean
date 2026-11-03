import Blotto.GeneralPaperPreparedSegmentCompaction

/-! Fused unsigned arithmetic for categorical preparation. Actual operands,
result, zero-test allowance, control and references are charged. -/
namespace Blotto.GeneralPaperNaturalScalarStep
set_option autoImplicit false

inductive Op where
  | add | mul | div

def Op.apply : Op → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .div, a, b => a / b

def word (a : ℕ) : ℕ := 1 + binaryWordWidth a

def run (model : RationalCostModel) (A : ℕ) (op : Op) (a b : ℕ) : ℕ × ℕ :=
  let value := op.apply a b
  (value, word a + word b + word value + 2 * model.rat (max (word a) (word b)) + 16 * A + 16)

theorem data (model : RationalCostModel) (A : ℕ) (op : Op) (a b : ℕ) : (run model A op a b).1 = op.apply a b := rfl

theorem work (model : RationalCostModel) (A : ℕ) (op : Op) (a b L : ℕ)
    (ha : word a ≤ L) (hb : word b ≤ L) (ho : word (op.apply a b) ≤ L) :
    (run model A op a b).2 ≤ 5 * model.rat L + 16 * A + 16 := by
  have h1 := ha.trans (model.word_le L)
  have h2 := hb.trans (model.word_le L)
  have h3 := ho.trans (model.word_le L)
  have h4 := model.monotone (max_le ha hb)
  unfold run
  dsimp only
  omega

end Blotto.GeneralPaperNaturalScalarStep
