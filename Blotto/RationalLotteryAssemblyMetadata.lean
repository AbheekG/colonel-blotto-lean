import Blotto.RationalLotteryTranslateBitCost
import Blotto.RationalExpressionMetadataAllowance
import Blotto.PreparedDescriptorMetadataWork

/-! Per-construction metadata for translated, binary and padded tables.
Every scalar formula environment is charged and all final slots are retained,
including zero weights. Child production/caller frequency and physical
addresses/backend/ownership/space remain separate. -/

namespace Blotto.RationalLotteryAssemblyCode

theorem environmentMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (p q : ℚ) (s : ℕ) (hp : RationalHeight p s) (hq : RationalHeight q s) :
    rationalEnvironmentMetadataWork primitive (environment p q) ≤ rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := by
  apply rationalEnvironmentMetadataWork_bound primitive c hPrimitive
  intro j
  fin_cases j
  · simpa [environment, FixedArrayTable.read_ofFn] using rationalWordWidth_of_height hp
  · simpa [environment, FixedArrayTable.read_ofFn] using rationalWordWidth_of_height hq

end Blotto.RationalLotteryAssemblyCode
namespace Blotto.RationalSegmentLottery
open scoped BigOperators

def shiftThirdMetadataWork {k : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (l : RationalSegmentLottery 3 k) (x : ℚ) : ℕ :=
  (∑ slot : Fin k, (rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment (l.P slot 2) x) +
    rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment (l.Q slot 2) x))) +
    (∑ slot : Fin k, (RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.sum (RationalLotteryAssemblyCode.environment (l.P slot 2) x) +
      RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.sum (RationalLotteryAssemblyCode.environment (l.Q slot 2) x))) +
      PreparedSegmentDescriptor.preparationMetadataBitWork primitive (l.shiftThird x)

theorem shiftThirdMetadataWork_bound {k : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (l : RationalSegmentLottery 3 k) (x : ℚ) (s : ℕ) (h : l.HeightAt s) (hx : RationalHeight x s) :
    shiftThirdMetadataWork primitive c l x ≤ 2 * k * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) +
      6 * k * RationalExpression.metadataInstructionBound c 2 3 +
        PreparedSegmentDescriptor.preparationMetadataBound c 3 k (expressionHeightBudget s 1) := by
  have hEnv : (∑ slot : Fin k, (rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment (l.P slot 2) x) +
      rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment (l.Q slot 2) x))) ≤
      2 * k * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin k, 2 * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := Finset.sum_le_sum (fun slot _ => by
        have hp := RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive _ x s (h.2 slot 2).1 hx
        have hq := RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive _ x s (h.2 slot 2).2 hx
        omega)
      _ = _ := by simp; ring
  have hPrograms : (∑ slot : Fin k, (RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.sum (RationalLotteryAssemblyCode.environment (l.P slot 2) x) +
      RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.sum (RationalLotteryAssemblyCode.environment (l.Q slot 2) x))) ≤
      6 * k * RationalExpression.metadataInstructionBound c 2 3 := by
    calc
      _ ≤ ∑ _slot : Fin k, 6 * RationalExpression.metadataInstructionBound c 2 3 := Finset.sum_le_sum (fun slot _ => by
        have hp := RationalExpression.metadataAllowance_uniform_bound c RationalLotteryAssemblyCode.sum
          (RationalLotteryAssemblyCode.environment (l.P slot 2) x) 2 3 le_rfl (by decide)
        have hq := RationalExpression.metadataAllowance_uniform_bound c RationalLotteryAssemblyCode.sum
          (RationalLotteryAssemblyCode.environment (l.Q slot 2) x) 2 3 le_rfl (by decide)
        omega)
      _ = _ := by simp; ring
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (h.shiftThird x hx)
  exact Nat.add_le_add (Nat.add_le_add hEnv hPrograms) hTable

def binaryMetadataWork {n k m : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) : ℕ :=
  (∑ slot : Fin k, rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment p (l.weight slot))) +
    (∑ slot : Fin m, rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment p (t.weight slot))) +
      (∑ slot : Fin k, RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.product (RationalLotteryAssemblyCode.environment p (l.weight slot))) +
        (∑ slot : Fin m, RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.complementProduct (RationalLotteryAssemblyCode.environment p (t.weight slot))) +
          PreparedSegmentDescriptor.preparationMetadataBitWork primitive (binary p hp l t)

theorem binaryMetadataWork_bound {n k m : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m)
    (s : ℕ) (hs : 2 ≤ s) (hP : RationalHeight p s) (hl : l.HeightAt s) (ht : t.HeightAt s) :
    binaryMetadataWork primitive c p hp l t ≤ (k + m) * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) +
      (3 * k + 5 * m) * RationalExpression.metadataInstructionBound c 2 5 +
        PreparedSegmentDescriptor.preparationMetadataBound c n (k + m) (expressionHeightBudget s 2) := by
  have hE : ∀ q, RationalHeight q s → rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment p q) ≤
      rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := fun q hq => RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive p q s hP hq
  have hLeftEnv : (∑ slot : Fin k, rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment p (l.weight slot))) ≤ k * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin k, rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := Finset.sum_le_sum (fun slot _ => hE _ (hl.1 slot))
      _ = _ := by simp
  have hRightEnv : (∑ slot : Fin m, rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment p (t.weight slot))) ≤ m * rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin m, rationalEnvironmentMetadataBound c 2 (1 + 2 * s) := Finset.sum_le_sum (fun slot _ => hE _ (ht.1 slot))
      _ = _ := by simp
  have hLeft : (∑ slot : Fin k, RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.product (RationalLotteryAssemblyCode.environment p (l.weight slot))) ≤
      3 * k * RationalExpression.metadataInstructionBound c 2 5 := by
    calc
      _ ≤ ∑ _slot : Fin k, 3 * RationalExpression.metadataInstructionBound c 2 5 := Finset.sum_le_sum (fun slot _ =>
        RationalExpression.metadataAllowance_uniform_bound c _ _ 2 3 le_rfl (by decide) |>.trans
          (Nat.mul_le_mul_left 3 (RationalExpression.metadataInstructionBound_mono c (le_refl 2) (by decide : 3 ≤ 5))))
      _ = _ := by simp; ring
  have hRight : (∑ slot : Fin m, RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.complementProduct (RationalLotteryAssemblyCode.environment p (t.weight slot))) ≤
      5 * m * RationalExpression.metadataInstructionBound c 2 5 := by
    calc
      _ ≤ ∑ _slot : Fin m, 5 * RationalExpression.metadataInstructionBound c 2 5 := Finset.sum_le_sum (fun slot _ =>
        RationalExpression.metadataAllowance_uniform_bound c _ _ 2 5 le_rfl (by decide))
      _ = _ := by simp; ring
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (hl.binary ht hs p hp hP)
  unfold binaryMetadataWork
  nlinarith

def paddingMetadataWork {n k : ℕ} (primitive : ℕ → ℕ) (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k) : ℕ :=
  PreparedSegmentDescriptor.preparationMetadataBitWork primitive (l.padRight m fallback)

theorem paddingMetadataWork_bound {n k : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k) (s : ℕ) (hs : 2 ≤ s) (h : l.HeightAt s) :
    paddingMetadataWork primitive l m fallback ≤ PreparedSegmentDescriptor.preparationMetadataBound c n (k + m) s :=
  PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (h.padRight hs m fallback)

end Blotto.RationalSegmentLottery
