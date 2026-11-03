import Blotto.GeneralPaperEqualPackingExecution

/-! Materialize the saturated equal-budget lengths once from the retained
positive integer weights. The common denominator is converted once; packing
and routing can subsequently read this array without evaluating a quotient. -/
namespace Blotto.GeneralPaperEqualLengthArray
open GeneralPaperRationalScalarStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def height (s : ℕ) : ℕ := expressionHeightBudget s 2

def coordinate (model : RationalCostModel) (A : ℕ) (D : ℚ) (a : ℕ) : ℚ × ℕ :=
  let numerator := natural A a
  let quotient := GeneralPaperRationalScalarStep.run model A .div numerator.1 D
  let doubled := GeneralPaperRationalScalarStep.run model A .mul 2 quotient.1
  (doubled.1, numerator.2 + quotient.2 + doubled.2 + 16 * A + 16)

theorem coordinate_data (model : RationalCostModel) (A : ℕ) (D : ℚ) (a : ℕ) :
    (coordinate model A D a).1 = 2 * ((a : ℚ) / D) := rfl

theorem coordinate_work (model : RationalCostModel) (A D a s : ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : a ≤ D) :
    (coordinate model A (D : ℚ) a).2 ≤ 12 * model.rat (1 + 2 * height s) + 64 * A + 64 := by
  have hS : s ≤ height s := expressionHeightBudget_ge_input s 2
  have hAWord := (binaryWordWidth_mono ha).trans hD
  have hNatA := DyadicMidpointAssembly.nat_height a s (by omega)
    ((lt_pow_binaryWordWidth a).trans_le (Nat.pow_le_pow_right (by decide) hAWord))
  have hNatD := DyadicMidpointAssembly.nat_height D s (by omega)
    ((lt_pow_binaryWordWidth D).trans_le (Nat.pow_le_pow_right (by decide) hD))
  have hTwo : RationalHeight (2 : ℚ) s :=
    (show RationalHeight (2 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hQuotient := hNatA.div hNatD
  have hDouble := hTwo.mul hQuotient
  have hQSize : s + s ≤ height s := by unfold height expressionHeightBudget; omega
  have hDSize : s + (s + s) ≤ height s := by unfold height expressionHeightBudget; omega
  have h1 := natural_work model A a (height s) (hNatA.mono hS) (by omega)
  have h2 := GeneralPaperRationalScalarStep.work model A .div (a : ℚ) (D : ℚ) (height s)
    (hNatA.mono hS) (hNatD.mono hS) (hQuotient.mono hQSize)
  have h3 := GeneralPaperRationalScalarStep.work model A .mul 2 ((a : ℚ) / D) (height s)
    (hTwo.mono hS) (hQuotient.mono hQSize) (hDouble.mono hDSize)
  unfold coordinate
  dsimp only [natural, GeneralPaperRationalScalarStep.run, Op.apply] at h1 h2 h3 ⊢
  omega

def run {n : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable n ℕ) (D : ℕ) :
    FixedArrayTable n ℚ × ℕ :=
  let denominator := natural A D
  let result := PaperIndexedArrayConstruction.run id A (fun j => coordinate model A denominator.1 (weights.read j))
  (result.1, denominator.2 + result.2 + 32 * A + 32)

theorem data {n : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable n ℕ) (D : ℕ) :
    (run model A weights D).1 = FixedArrayTable.ofFn (fun j => 2 * ((weights.read j : ℚ) / D)) := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

theorem work {n : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable n ℕ) (D s : ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D) :
    (run model A weights D).2 ≤ (12 * n + 2) * model.rat (1 + 2 * height s) +
      64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n := by
  have hS : s ≤ height s := expressionHeightBudget_ge_input s 2
  have hNatD := DyadicMidpointAssembly.nat_height D s (by omega)
    ((lt_pow_binaryWordWidth D).trans_le (Nat.pow_le_pow_right (by decide) hD))
  have hDen := natural_work model A D (height s) (hNatD.mono hS) (by omega)
  have hRows : (∑ j, (coordinate model A (D : ℚ) (weights.read j)).2) ≤
      n * (12 * model.rat (1 + 2 * height s) + 64 * A + 64) := by
    calc
      _ ≤ ∑ _j : Fin n, (12 * model.rat (1 + 2 * height s) + 64 * A + 64) :=
        Finset.sum_le_sum (fun j _ => coordinate_work model A D (weights.read j) s hs hD (ha j))
      _ = _ := by simp
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  dsimp only [natural] at hDen ⊢
  nlinarith only [hDen, hRows]

end Blotto.GeneralPaperEqualLengthArray
