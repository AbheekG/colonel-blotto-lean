import Blotto.GeneralPaperThreeStaticBounds

/-! Eager segment arrays built by the fused priced evaluator. Program
correctness is an erased index; only the actual environment and fixed code
are read. All callbacks execute once, including zero-weight endpoint slots. -/
namespace Blotto.GeneralPaperSegmentExpressionCompiler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000

structure Programs {n r k : ℕ} (l : RationalSegmentLottery n r) (env : FixedArrayTable k ℚ) where
  weight : Fin r → RationalExpression k
  left : Fin r → Fin n → RationalExpression k
  right : Fin r → Fin n → RationalExpression k
  weight_correct : ∀ i, ((weight i).run env).1 = l.weight i
  left_correct : ∀ i j, ((left i j).run env).1 = l.P i j
  right_correct : ∀ i j, ((right i j).run env).1 = l.Q i j

def row {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) : FixedArrayTable n ℚ × ℕ :=
  PaperIndexedArrayConstruction.run id A (fun j => GeneralPaperExpressionBitExecution.run model A env (programs j))

theorem row_data {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) :
    (row model A env programs).1 = FixedArrayTable.ofFn (fun j => ((programs j).run env).1) := by
  rw [row, PaperIndexedArrayConstruction.run_data]
  simp only [GeneralPaperExpressionBitExecution.data]

def run {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (programs : Programs l env) : PreparedSegmentDescriptor l × ℕ :=
  let weights := row model A env programs.weight
  let left := PaperIndexedArrayConstruction.run id A (fun i =>
    let actual := row model A env (programs.left i)
    (actual.1, actual.2 + 32 * A + 32))
  let right := PaperIndexedArrayConstruction.run id A (fun i =>
    let actual := row model A env (programs.right i)
    (actual.1, actual.2 + 32 * A + 32))
  let descriptor : PreparedSegmentDescriptor l :=
    ⟨weights.1, left.1, right.1,
      (by intro i; rw [row_data, FixedArrayTable.read_ofFn]; exact programs.weight_correct i),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn, row_data,
          FixedArrayTable.read_ofFn]; exact programs.left_correct i j),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn, row_data,
          FixedArrayTable.read_ofFn]; exact programs.right_correct i j)⟩
  (descriptor, weights.2 + left.2 + right.2 + 64 * A + 64)

theorem unique {n r : ℕ} {l : RationalSegmentLottery n r} (a b : PreparedSegmentDescriptor l) : a = b := by
  have hw := GeneralPaperNativeQuantizedLabels.table_ext a.weights b.weights
    (fun i => (a.weight_correct i).trans (b.weight_correct i).symm)
  have hp := GeneralPaperNativeQuantizedLabels.table_ext a.left b.left (fun i =>
    GeneralPaperNativeQuantizedLabels.table_ext (a.left.read i) (b.left.read i)
      (fun j => (a.left_correct i j).trans (b.left_correct i j).symm))
  have hq := GeneralPaperNativeQuantizedLabels.table_ext a.right b.right (fun i =>
    GeneralPaperNativeQuantizedLabels.table_ext (a.right.read i) (b.right.read i)
      (fun j => (a.right_correct i j).trans (b.right_correct i j).symm))
  cases a
  cases b
  cases hw
  cases hp
  cases hq
  rfl

theorem data {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (programs : Programs l env) :
    (run model A env programs).1 = PreparedSegmentDescriptor.prepare l := unique _ _

theorem row_work {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (C : ℕ)
    (hC : ∀ j, (GeneralPaperExpressionBitExecution.run model A env (programs j)).2 ≤ C) :
    (row model A env programs).2 ≤ n * C + PaperIndexedArrayConstruction.overhead id A n n := by
  rw [row, PaperIndexedArrayConstruction.run_work]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hC j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using Nat.add_le_add_right h _

def bound (A n r C : ℕ) : ℕ :=
  (r + 2 * r * n) * C + 3 * PaperIndexedArrayConstruction.overhead id A r r +
    2 * r * PaperIndexedArrayConstruction.overhead id A n n + 64 * (r + 1) * (A + 1)

theorem matrix_work {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (C : ℕ)
    (hC : ∀ i j, (GeneralPaperExpressionBitExecution.run model A env (programs i j)).2 ≤ C) :
    (PaperIndexedArrayConstruction.run id A (fun i =>
      let actual := row model A env (programs i)
      (actual.1, actual.2 + 32 * A + 32))).2 ≤
      r * (n * C + PaperIndexedArrayConstruction.overhead id A n n + 32 * A + 32) +
        PaperIndexedArrayConstruction.overhead id A r r := by
  rw [PaperIndexedArrayConstruction.run_work]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Nat.add_le_add_right (Nat.add_le_add_right (row_work model A env (programs i) C (hC i)) (32 * A)) 32)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using Nat.add_le_add_right h _

theorem work {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (programs : Programs l env) (C : ℕ)
    (hw : ∀ i, (GeneralPaperExpressionBitExecution.run model A env (programs.weight i)).2 ≤ C)
    (hp : ∀ i j, (GeneralPaperExpressionBitExecution.run model A env (programs.left i j)).2 ≤ C)
    (hq : ∀ i j, (GeneralPaperExpressionBitExecution.run model A env (programs.right i j)).2 ≤ C) :
    (run model A env programs).2 ≤ bound A n r C := by
  have hW := row_work model A env programs.weight C hw
  have hP := matrix_work model A env programs.left C hp
  have hQ := matrix_work model A env programs.right C hq
  unfold run bound
  dsimp only
  nlinarith only [hW, hP, hQ]

end Blotto.GeneralPaperSegmentExpressionCompiler
