import Blotto.RationalEnvironmentMetadata

/-! Control/index/counter allowance for the selected counted expression path.
Index and operation-counter arguments fit the syntax/input cap. Scalar rational
operands retain their separate Rat prices; addresses/records/backend remain
outside this integer-control allowance. -/

namespace Blotto.RationalExpression

def metadataInstructionBound (c inputCount operationCap : ℕ) : ℕ :=
  (16 + 6 * c) * binaryWordWidth (inputCount + operationCap + 2) + 10

theorem metadataInstructionBound_mono (c : ℕ) {k K a A : ℕ} (hk : k ≤ K) (ha : a ≤ A) :
    metadataInstructionBound c k a ≤ metadataInstructionBound c K A := by
  unfold metadataInstructionBound
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (binaryWordWidth_mono (by omega))) 10

def metadataAllowance {k : ℕ} (c : ℕ) (e : RationalExpression k) (env : FixedArrayTable k ℚ) : ℕ :=
  (e.run env).2 * metadataInstructionBound c k e.operationBound

theorem metadataAllowance_bound {k : ℕ} (c : ℕ) (e : RationalExpression k) (env : FixedArrayTable k ℚ) :
    metadataAllowance c e env ≤ e.operationBound * metadataInstructionBound c k e.operationBound :=
  Nat.mul_le_mul_right _ (e.run_operations_le env)

theorem metadataAllowance_uniform_bound {k : ℕ} (c : ℕ) (e : RationalExpression k) (env : FixedArrayTable k ℚ)
    (K A : ℕ) (hk : k ≤ K) (hA : e.operationBound ≤ A) :
    metadataAllowance c e env ≤ A * metadataInstructionBound c K A :=
  (metadataAllowance_bound c e env).trans (Nat.mul_le_mul hA (metadataInstructionBound_mono c hk hA))

def metadataInstructionBitPrice (primitive : ℕ → ℕ) (indices : List ℕ) : ℕ :=
  (indices.map (fun x => binaryWordWidth x + primitive (binaryWordWidth x))).sum

theorem metadataInstructionBitPrice_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (indices : List ℕ) (cap : ℕ) (hCap : ∀ x ∈ indices, x ≤ cap)
    (hCount : indices.length ≤ 6) :
    metadataInstructionBitPrice primitive indices ≤ 6 * (1 + c) * binaryWordWidth (cap + 1) := by
  have hPoint : ∀ x ∈ indices, binaryWordWidth x + primitive (binaryWordWidth x) ≤ (1 + c) * binaryWordWidth (cap + 1) := by
    intro x hx
    have hW := binaryWordWidth_mono (show x ≤ cap + 1 from (hCap x hx).trans (by omega))
    have hp := (hPrimitive (binaryWordWidth x)).trans (Nat.mul_le_mul_left c hW)
    nlinarith
  have hSum : (indices.map (fun x => binaryWordWidth x + primitive (binaryWordWidth x))).sum ≤
      indices.length * ((1 + c) * binaryWordWidth (cap + 1)) := by
    clear hCount
    induction indices with
    | nil => simp
    | cons x xs ih =>
      have hx := hPoint x (by simp)
      have hr := ih (fun y hy => hCap y (by simp [hy])) (fun y hy => hPoint y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  unfold metadataInstructionBitPrice
  have hCapPrice := Nat.mul_le_mul_right ((1 + c) * binaryWordWidth (cap + 1)) hCount
  have hConstant : 6 * ((1 + c) * binaryWordWidth (cap + 1)) = 6 * (1 + c) * binaryWordWidth (cap + 1) := by ring
  exact hSum.trans (hCapPrice.trans_eq hConstant)

end Blotto.RationalExpression
