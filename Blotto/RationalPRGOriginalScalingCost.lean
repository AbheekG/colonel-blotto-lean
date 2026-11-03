import Blotto.RationalPRGOutputHeight
import Blotto.RationalScaleRowCost
import Blotto.RationalPRGOriginalProcessing

/-! Original-budget output scaling prices the exact primary sampler's row,
including every exhaustion path. The processing ledger is then composed once
with this output pass. These remain labelled bit-work bounds. -/

namespace Blotto.RationalPRGOriginalInput

def richScalingBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  RationalScaleRowCode.rowBitCost model i.a (i.normalizedInput.richSample K bits)

def poorScalingBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  RationalScaleRowCode.rowBitCost model i.a (i.normalizedInput.poorSample K bits)

def scalingWidth {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  1 + 2 * expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 76

theorem scalingBitWork_bounds {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richScalingBitWork model K bits ≤ 4 * n * model.rat (i.scalingWidth K) ∧
      i.poorScalingBitWork model K bits ≤ 4 * n * model.rat (i.scalingWidth K) := by
  let t := expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 75
  have ht : 3 + i.originalInputWordWidth ≤ t :=
    (le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)
  have hWidth : 1 + 2 * ((3 + i.originalInputWordWidth) + t) ≤ i.scalingWidth K := by
    unfold scalingWidth
    rw [expressionHeightBudget_succ]
    change 1 + 2 * ((3 + i.originalInputWordWidth) + t) ≤ 1 + 2 * (2 * t + 1)
    omega
  have hPrice := Nat.mul_le_mul_left (4 * n) (model.monotone hWidth)
  exact ⟨(RationalScaleRowCode.rowBitCost_bound model i.a (i.normalizedInput.richSample K bits)
      _ t i.scale_height (fun j => (i.normalized_sample_heights K bits j).1)).trans hPrice,
    (RationalScaleRowCode.rowBitCost_bound model i.a (i.normalizedInput.poorSample K bits)
      _ t i.scale_height (fun j => (i.normalized_sample_heights K bits j).2)).trans hPrice⟩

noncomputable def richProcessingAndScalingWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.normalizedInput.richSharedProcessingWork model primitive copyResources K bits + i.richScalingBitWork model K bits

noncomputable def poorProcessingAndScalingWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.normalizedInput.poorSharedProcessingWork model primitive copyResources K bits + i.poorScalingBitWork model K bits

theorem richProcessingAndScalingWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richProcessingAndScalingWork model primitive copyResources K bits ≤
      (32 * n + 15) * model.rat i.processingSourceWidth + i.processingCouplingBound model c K +
        2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) :=
  Nat.add_le_add (i.normalized_richProcessingWork_bound model primitive c hPrimitive copyResources K bits)
    (i.scalingBitWork_bounds model K bits).1

theorem poorProcessingAndScalingWork_logical_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorProcessingAndScalingWork model primitive false K bits ≤
      (192 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) :=
  Nat.add_le_add (i.normalized_poorProcessingWork_logical_bound model primitive c hPrimitive K bits)
    (i.scalingBitWork_bounds model K bits).2

theorem poorProcessingAndScalingWork_fullCopy_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorProcessingAndScalingWork model primitive true K bits ≤
      (2 * n * n + 188 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) :=
  Nat.add_le_add (i.normalized_poorProcessingWork_fullCopy_bound model primitive c hPrimitive K bits)
    (i.scalingBitWork_bounds model K bits).2

end Blotto.RationalPRGOriginalInput
