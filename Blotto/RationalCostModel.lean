import Blotto.RationalExpressionWordWidth

/-! Explicit rational-primitive cost profiles as in the paper's Rat(W).
A profile is a mathematical majorant, not a claim about a compiler/library.
Word copies are included by dominance; primitive implementation contracts are
provided separately when interpreting a priced algorithm as physical bit work. -/

namespace Blotto

structure RationalCostModel where
  rat : ℕ → ℕ
  monotone : Monotone rat
  word_le : ∀ w, w ≤ rat w
  superadditive : ∀ a b, rat a + rat b ≤ rat (a + b)

namespace RationalCostModel

theorem copy_le (model : RationalCostModel) {a b : ℕ} (hab : a ≤ b) : a ≤ model.rat b :=
  hab.trans (model.word_le b)

theorem priced_le (model : RationalCostModel) {a b : ℕ} (hab : a ≤ b) : model.rat a ≤ model.rat b := model.monotone hab

theorem list_sum_le (model : RationalCostModel) (widths : List ℕ) :
    (widths.map model.rat).sum ≤ model.rat widths.sum := by
  induction widths with
  | nil => simp
  | cons w rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (Nat.add_le_add_left ih _).trans (model.superadditive w rest.sum)

theorem list_uniform_bound (model : RationalCostModel) (widths : List ℕ) (w : ℕ)
    (h : ∀ a ∈ widths, a ≤ w) : (widths.map model.rat).sum ≤ widths.length * model.rat w := by
  induction widths with
  | nil => simp
  | cons a rest ih =>
    have ha := model.monotone (h a (by simp))
    have hr := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

-- This concrete profile represents a conservative schoolbook size envelope.
-- It is not a proof that a particular library realizes that envelope.
def schoolbook : RationalCostModel where
  rat := fun w => w * w + w
  monotone := by intro a b h; nlinarith
  word_le := by intro w; omega
  superadditive := by intro a b; nlinarith

end RationalCostModel
end Blotto
