import Blotto.RationalThreeCompilerMetadata
import Blotto.RationalOverlapFormulaHeight

/-! The overlap compiler constructs an environment for every weight and safe
endpoint formula. All nine environment invocations per slot and repeated product
index decoding are charged; no CSE is assumed. Parent production and physical
addresses/backend/records/ownership/space remain separate. -/

namespace Blotto.RationalOverlapFormula
open scoped BigOperators
open OverlapFormulaCode

def slotIndexMetadataWork (primitive : ℕ → ℕ) (k h : ℕ) : ℕ :=
  ∑ slot : Fin (k * h), (6 * binaryWordWidth (k * h + h + k + 2) +
    2 * primitive (max (binaryWordWidth slot.val) (binaryWordWidth h)) + 4)

def slotIndexMetadataUnitBound (c k h : ℕ) : ℕ :=
  (6 + 2 * c) * binaryWordWidth (k * h + h + k + 2) + 4

theorem slotIndexMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (k h : ℕ) :
    slotIndexMetadataWork primitive k h ≤ (k * h) * slotIndexMetadataUnitBound c k h := by
  have hPoint : ∀ slot : Fin (k * h), 6 * binaryWordWidth (k * h + h + k + 2) +
      2 * primitive (max (binaryWordWidth slot.val) (binaryWordWidth h)) + 4 ≤ slotIndexMetadataUnitBound c k h := by
    intro slot
    have hIndex := binaryWordWidth_mono (show slot.val ≤ k * h + h + k + 2 by omega)
    have hCount := binaryWordWidth_mono (show h ≤ k * h + h + k + 2 by omega)
    have hPrice := (hPrimitive (max (binaryWordWidth slot.val) (binaryWordWidth h))).trans
      (Nat.mul_le_mul_left c (max_le hIndex hCount))
    unfold slotIndexMetadataUnitBound
    nlinarith
  calc
    _ ≤ ∑ _slot : Fin (k * h), slotIndexMetadataUnitBound c k h := Finset.sum_le_sum (fun slot _ => hPoint slot)
    _ = _ := by simp

def expressionMetadataWork {k h : ℕ} (c : ℕ) (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  (∑ slot : Fin (k * h), RationalExpression.metadataAllowance c weight (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, RationalExpression.metadataAllowance c (safeP r) (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) +
      (∑ slot : Fin (k * h), ∑ r : Fin 4, RationalExpression.metadataAllowance c (safeQ r) (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2))

theorem expressionMetadataWork_bound {k h : ℕ} (c : ℕ) (G : RationalOverlapGluing k h) (B : ℚ) :
    expressionMetadataWork c G B ≤ 2176 * (k * h) * RationalExpression.metadataInstructionBound c 16 256 := by
  let P := RationalExpression.metadataInstructionBound c 16 256
  have hw : ∀ i j, RationalExpression.metadataAllowance c weight (environment G B i j) ≤ 128 * P := by
    intro i j
    have hCount := weight_operations G B i j
    have hUnit := RationalExpression.metadataInstructionBound_mono c (le_refl 16) (weight_operationBound.trans (by decide : 128 ≤ 256))
    exact Nat.mul_le_mul hCount hUnit
  have hp : ∀ i j r, RationalExpression.metadataAllowance c (safeP r) (environment G B i j) ≤ 256 * P :=
    fun i j r => RationalExpression.metadataAllowance_uniform_bound c _ _ 16 256 le_rfl (safeP_operationBound r)
  have hq : ∀ i j r, RationalExpression.metadataAllowance c (safeQ r) (environment G B i j) ≤ 256 * P :=
    fun i j r => RationalExpression.metadataAllowance_uniform_bound c _ _ 16 256 le_rfl (safeQ_operationBound r)
  have hW : (∑ slot : Fin (k * h), RationalExpression.metadataAllowance c weight (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (128 * P) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), 128 * P := Finset.sum_le_sum (fun slot _ => hw _ _)
      _ = _ := by simp
  have hP : (∑ slot : Fin (k * h), ∑ r : Fin 4, RationalExpression.metadataAllowance c (safeP r) (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (1024 * P) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => hp _ _ r))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hQ : (∑ slot : Fin (k * h), ∑ r : Fin 4, RationalExpression.metadataAllowance c (safeQ r) (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (1024 * P) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => hq _ _ r))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  unfold expressionMetadataWork
  change _ ≤ 2176 * (k * h) * P
  nlinarith

def compilerMetadataWork {k h : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  9 * (∑ slot : Fin (k * h), rationalEnvironmentMetadataWork primitive (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) +
    expressionMetadataWork c G B + 9 * slotIndexMetadataWork primitive k h +
      PreparedSegmentDescriptor.preparationMetadataBitWork primitive (descriptorReference G B)

theorem compilerMetadataWork_bound {k h : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (G : RationalOverlapGluing k h) (B : ℚ) (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    compilerMetadataWork primitive c G B ≤ 9 * ((k * h) * rationalEnvironmentMetadataBound c 16 (1 + 2 * s)) +
      2176 * (k * h) * RationalExpression.metadataInstructionBound c 16 256 +
        9 * ((k * h) * slotIndexMetadataUnitBound c k h) +
          PreparedSegmentDescriptor.preparationMetadataBound c 4 (k * h) (expressionHeightBudget s 9) := by
  have hEnv : (∑ slot : Fin (k * h), rationalEnvironmentMetadataWork primitive (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤
      (k * h) * rationalEnvironmentMetadataBound c 16 (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), rationalEnvironmentMetadataBound c 16 (1 + 2 * s) := Finset.sum_le_sum (fun slot _ =>
        rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun r => rationalWordWidth_of_height
          (environment_height G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2 s hFirst hSecond hD hB r)))
      _ = _ := by simp
  have hExpressions := expressionMetadataWork_bound c G B
  have hIndices := slotIndexMetadataWork_bound primitive c hPrimitive k h
  have hReference : (descriptorReference G B).HeightAt (expressionHeightBudget s 9) := by
    rw [descriptorReference_eq]
    exact (G.descriptor_height B s hs hFirst hSecond hD hB).mono (expressionHeightBudget_mono s (by decide : 6 ≤ 9))
  have hDescriptor := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ hReference
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 9 hEnv) hExpressions) (Nat.mul_le_mul_left 9 hIndices)) hDescriptor

end Blotto.RationalOverlapFormula
