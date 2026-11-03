import Blotto.GeneralPaperEqualPreparationPrefix

/-! One coefficient and selected-entry reference-array write per member.
Lengths are read from the materialized array and the group total is passed
once. Source rational operands/results, labels, addresses and control are
priced explicitly in the paper's mutable reference-array convention. -/
namespace Blotto.GeneralPaperEqualRouteMembers
open GeneralPaperRationalScalarStep (Op)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run {n m : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) : List (Fin n) → FixedArrayTable n (GroupRoute m) → FixedArrayTable n (GroupRoute m) × ℕ
  | [], table => (table, 16 * A + 16)
  | j :: rest, table =>
      let coefficient := GeneralPaperRationalScalarStep.run model A .div (values.read j) total
      let written := table.write j (some g, coefficient.1)
      let child := run model A values g total rest written
      (child.1, coefficient.2 +
        32 * (A + binaryWordWidth (j.val + 1) + binaryWordWidth (g.val + 1) + 1) + child.2)

theorem data {n m : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m)) :
    (run model A values g total items table).1 =
      table.patch (items.map (fun j => (j, (some g, values.read j / total)))) := by
  induction items generalizing table with
  | nil => rfl
  | cons j rest ih =>
    rw [run]
    dsimp only
    rw [ih]
    rfl

def height (s : ℕ) : ℕ := expressionHeightBudget s 1

def stepBound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  5 * model.rat (1 + 2 * height s) +
    64 * (A + binaryWordWidth (n + 1) + binaryWordWidth (m + 1) + 1)

theorem step_work {n m s : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (j : Fin n) (hv : RationalHeight (values.read j) s) (ht : RationalHeight total s) :
    (GeneralPaperRationalScalarStep.run model A .div (values.read j) total).2 +
      32 * (A + binaryWordWidth (j.val + 1) + binaryWordWidth (g.val + 1) + 1) ≤ stepBound model A n m s := by
  have hs := expressionHeightBudget_ge_input s 1
  have hq : s + s ≤ height s := by unfold height expressionHeightBudget; omega
  have h := GeneralPaperRationalScalarStep.work model A .div (values.read j) total (height s)
    (hv.mono hs) (ht.mono hs) ((hv.div ht).mono hq)
  have hj := binaryWordWidth_mono (show j.val + 1 ≤ n + 1 by omega)
  have hg := binaryWordWidth_mono (show g.val + 1 ≤ m + 1 by omega)
  unfold stepBound
  omega

theorem work {n m s : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m))
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : RationalHeight total s) :
    (run model A values g total items table).2 ≤ items.length * stepBound model A n m s + 16 * A + 16 := by
  induction items generalizing table with
  | nil => simp only [run, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons j rest ih =>
    have hStep := step_work model A values g total j (hv j) ht
    have hChild := ih (table.write j (some g, (GeneralPaperRationalScalarStep.run model A .div (values.read j) total).1))
    rw [run]
    dsimp only
    simp only [List.length_cons]
    nlinarith only [hStep, hChild]

end Blotto.GeneralPaperEqualRouteMembers
