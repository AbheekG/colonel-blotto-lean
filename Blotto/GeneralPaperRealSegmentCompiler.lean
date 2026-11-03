import Blotto.GeneralPaperEqualRealCache

/-! Eager real-model segment compilation executes the existing counted
arithmetic programs once per entry. Indexed storage/control has unit cost;
neither word lengths nor exact-integer categorical data are computed. -/
namespace Blotto.GeneralPaperRealSegmentCompiler
open scoped BigOperators
open GeneralPaperSegmentExpressionCompiler (Programs)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem overhead (n k : ℕ) : PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 n k = 42 * k + 18 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [PaperIndexedArrayConstruction.overhead, PaperIndexedArrayConstruction.stepWork, ih]; omega

theorem array_work {n : ℕ} {α : Type*} (callback : Fin n → α × ℕ) (C : ℕ)
    (h : ∀ j, (callback j).2 ≤ C) :
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 callback).2 ≤ n * (C + 42) + 18 := by
  rw [PaperIndexedArrayConstruction.run_work, overhead]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  nlinarith only [hs]

def row {n k : ℕ} (env : FixedArrayTable k ℚ) (programs : Fin n → RationalExpression k) : FixedArrayTable n ℚ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun j =>
    let actual := (programs j).run env
    (actual.1, 8 * actual.2 + 32))

theorem row_data {n k : ℕ} (env : FixedArrayTable k ℚ) (programs : Fin n → RationalExpression k) :
    (row env programs).1 = FixedArrayTable.ofFn (fun j => ((programs j).run env).1) :=
  PaperIndexedArrayConstruction.run_data _ _ _

def run {n r k : ℕ} {l : RationalSegmentLottery n r} (env : FixedArrayTable k ℚ)
    (programs : Programs l env) : PreparedSegmentDescriptor l × ℕ :=
  let weights := row env programs.weight
  let left := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    let actual := row env (programs.left i)
    (actual.1, actual.2 + 32))
  let right := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    let actual := row env (programs.right i)
    (actual.1, actual.2 + 32))
  let descriptor : PreparedSegmentDescriptor l :=
    ⟨weights.1, left.1, right.1,
      (by intro i; rw [row_data, FixedArrayTable.read_ofFn]; exact programs.weight_correct i),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn, row_data,
          FixedArrayTable.read_ofFn]; exact programs.left_correct i j),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn, row_data,
          FixedArrayTable.read_ofFn]; exact programs.right_correct i j)⟩
  (descriptor, weights.2 + left.2 + right.2 + 128)

theorem data {n r k : ℕ} {l : RationalSegmentLottery n r} (env : FixedArrayTable k ℚ) (programs : Programs l env) :
    (run env programs).1 = PreparedSegmentDescriptor.prepare l :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem row_work {n k : ℕ} (env : FixedArrayTable k ℚ) (programs : Fin n → RationalExpression k) (C : ℕ)
    (h : ∀ j, (programs j).operationBound ≤ C) : (row env programs).2 ≤ n * (8 * C + 74) + 18 := by
  rw [row, PaperIndexedArrayConstruction.run_work, overhead]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Nat.add_le_add_right (Nat.mul_le_mul_left 8 (((programs j).run_operations_le env).trans (h j))) 32)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  nlinarith only [hs]

def bound (n r C : ℕ) : ℕ := (r + 2 * r * n) * (8 * C + 74) + 184 * r + 182

theorem matrix_work {n r k : ℕ} (env : FixedArrayTable k ℚ) (programs : Fin r → Fin n → RationalExpression k)
    (C : ℕ) (h : ∀ i j, (programs i j).operationBound ≤ C) :
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
      let actual := row env (programs i); (actual.1, actual.2 + 32))).2 ≤
      r * (n * (8 * C + 74) + 92) + 18 := by
  rw [PaperIndexedArrayConstruction.run_work, overhead]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Nat.add_le_add_right (row_work env _ C (h i)) 32)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  nlinarith only [hs]

theorem work {n r k : ℕ} {l : RationalSegmentLottery n r} (env : FixedArrayTable k ℚ) (programs : Programs l env)
    (C : ℕ) (hw : ∀ i, (programs.weight i).operationBound ≤ C)
    (hp : ∀ i j, (programs.left i j).operationBound ≤ C) (hq : ∀ i j, (programs.right i j).operationBound ≤ C) :
    (run env programs).2 ≤ bound n r C := by
  have hW := row_work env programs.weight C hw
  have hP := matrix_work env programs.left C hp
  have hQ := matrix_work env programs.right C hq
  unfold run bound
  dsimp only
  nlinarith only [hW, hP, hQ]

end Blotto.GeneralPaperRealSegmentCompiler
