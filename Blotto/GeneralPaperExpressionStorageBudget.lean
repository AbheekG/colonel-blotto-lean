import Blotto.GeneralPaperEqualLengthReturnStorage

/-! Local storage budgets for the actual fused expression evaluator.
Primitive scratch uses only the reached scalar/GeneralPaperExpressionBitExecution.compare charge. The separate
frame envelope covers fixed controls/references and bounded price counters;
borrowed environment and fixed program code belong to the calling owner. -/
namespace Blotto.GeneralPaperExpressionStorageBudget
open GeneralPaperExpressionBitExecution (run unit)
open GeneralPaperEncodedScalarStorage (natBits fields fields_bound)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem written_unit {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) : rationalWordWidth (run model A env e).1 + unit A env.data.size ≤ (run model A env e).2 := by
  induction e with
  | input j => exact le_rfl
  | literal q => exact le_rfl
  | add a b _ha _hb =>
    have h := GeneralPaperEqualLengthAllocationJoin.scalar_written model A .add (run model A env a).1 (run model A env b).1
    rw [run]
    dsimp only
    omega
  | sub a b _ha _hb =>
    have h := GeneralPaperEqualLengthAllocationJoin.scalar_written model A .sub (run model A env a).1 (run model A env b).1
    rw [run]
    dsimp only
    omega
  | mul a b _ha _hb =>
    have h := GeneralPaperEqualLengthAllocationJoin.scalar_written model A .mul (run model A env a).1 (run model A env b).1
    rw [run]
    dsimp only
    omega
  | div a b _ha _hb =>
    have h := GeneralPaperEqualLengthAllocationJoin.scalar_written model A .div (run model A env a).1 (run model A env b).1
    rw [run]
    dsimp only
    omega
  | minimum a b ha hb | maximum a b ha hb =>
    rw [run]
    dsimp only
    omega
  | ifLe a b yes no ha hb hy hn =>
    rw [run]
    dsimp only
    split_ifs <;> omega

theorem unit_le {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) : unit A env.data.size ≤ (run model A env e).2 := by
  have h := written_unit model A env e
  omega

theorem written {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) : rationalWordWidth (run model A env e).1 ≤ (run model A env e).2 := by
  have h := written_unit model A env e
  omega

def frameEnvelope (A k F : ℕ) : ℕ := 256 * (A + natBits (k + 1) + natBits (F + 1) + 1)

theorem frame_bound (A k F : ℕ) (hU : unit A k ≤ F) : frameEnvelope A k F ≤ 1024 * F := by
  have hBits : natBits (F + 1) ≤ F + 3 := by
    have h := Nat.log2_le_self (F + 1)
    change 1 + ((F + 1).log2 + 1) ≤ F + 3
    omega
  have hk := binaryWordWidth_pos (k + 1)
  have hControl : A + natBits (k + 1) ≤ F := by
    unfold unit at hU
    unfold natBits
    omega
  have hPositive : 64 ≤ F := by unfold unit at hU; omega
  unfold frameEnvelope
  omega

theorem frame_fields_bound (A k F : ℕ) (indices counters : List ℕ)
    (hi : indices.length ≤ 4) (hc : counters.length ≤ 16)
    (hIndex : ∀ x ∈ indices, x ≤ k) (hCounter : ∀ x ∈ counters, x ≤ F) :
    fields A indices + fields A counters + 64 * A + 64 ≤ frameEnvelope A k F := by
  have hI := fields_bound A (natBits (k + 1)) indices (fun x hx =>
    Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ k + 1 by have h := hIndex x hx; omega)) 1)
  have hC := fields_bound A (natBits (F + 1)) counters (fun x hx =>
    Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ F + 1 by have h := hCounter x hx; omega)) 1)
  have hIScale := Nat.mul_le_mul_right (natBits (k + 1) + A) hi
  have hCScale := Nat.mul_le_mul_right (natBits (F + 1) + A) hc
  unfold frameEnvelope
  omega

def scalarFrame (model : RationalCostModel) (A : ℕ) (op : GeneralPaperRationalScalarStep.Op) (a b : ℚ) : ℕ :=
  let actual := GeneralPaperRationalScalarStep.run model A op a b
  rationalWordWidth a + rationalWordWidth b + rationalWordWidth actual.1 + actual.2 +
    fields A [actual.2, 16 * A, 16] + 64 * A

theorem scalar_frame_bound (model : RationalCostModel) (A : ℕ) (op : GeneralPaperRationalScalarStep.Op) (a b : ℚ) :
    scalarFrame model A op a b ≤ 32 * (GeneralPaperRationalScalarStep.run model A op a b).2 := by
  let actual := GeneralPaperRationalScalarStep.run model A op a b
  have hCost : rationalWordWidth a + rationalWordWidth b + rationalWordWidth actual.1 + 16 * A + 16 ≤ actual.2 := by
    unfold actual GeneralPaperRationalScalarStep.run
    dsimp only
    omega
  have hFields := fields_bound A (natBits actual.2) [actual.2, 16 * A, 16] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A [actual.2, 16 * A, 16] ≤ 3 * (natBits actual.2 + A) + 32 * A at hFields
  have hBits : natBits actual.2 ≤ actual.2 + 2 := by
    have h := Nat.log2_le_self actual.2
    change 1 + (actual.2.log2 + 1) ≤ actual.2 + 2
    omega
  change rationalWordWidth a + rationalWordWidth b + rationalWordWidth actual.1 + actual.2 +
    fields A [actual.2, 16 * A, 16] + 64 * A ≤ 32 * actual.2
  omega

def compareFrame (model : RationalCostModel) (A : ℕ) (a b : ℚ) : ℕ :=
  let actual := GeneralPaperExpressionBitExecution.compare model A a b
  rationalWordWidth a + rationalWordWidth b + actual.2 + fields A [actual.2, 32 * A, 32] + 64 * A

theorem compare_frame_bound (model : RationalCostModel) (A : ℕ) (a b : ℚ) :
    compareFrame model A a b ≤ 32 * (GeneralPaperExpressionBitExecution.compare model A a b).2 := by
  let actual := GeneralPaperExpressionBitExecution.compare model A a b
  have hCost : rationalWordWidth a + rationalWordWidth b + 32 * A + 32 ≤ actual.2 := by
    unfold actual GeneralPaperExpressionBitExecution.compare
    dsimp only
    omega
  have hFields := fields_bound A (natBits actual.2) [actual.2, 32 * A, 32] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A [actual.2, 32 * A, 32] ≤ 3 * (natBits actual.2 + A) + 32 * A at hFields
  have hBits : natBits actual.2 ≤ actual.2 + 2 := by
    have h := Nat.log2_le_self actual.2
    change 1 + (actual.2.log2 + 1) ≤ actual.2 + 2
    omega
  change rationalWordWidth a + rationalWordWidth b + actual.2 + fields A [actual.2, 32 * A, 32] + 64 * A ≤ 32 * actual.2
  omega

end Blotto.GeneralPaperExpressionStorageBudget
