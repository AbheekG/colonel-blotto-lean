import Blotto.RationalPRGOutputEncodingCost
import Blotto.RationalPRGNormalizationCost

/-! A common bound for selected rich/poor sampling, including normalization,
processing, original-budget scaling and output framing. Both resource-store
interpretations remain explicit. This is labelled work; metadata/physical
backend/ownership/space are separate. -/

namespace Blotto.RationalPRGOriginalInput

def processingSourceCoefficient (n : ℕ) (copyResources : Bool) : ℕ :=
  if copyResources then 2 * n * n + 188 * n + 15 else 192 * n + 15

def dispatchBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c : ℕ)
    (copyResources : Bool) (K : ℕ) : ℕ :=
  5 * model.rat (1 + 2 * i.originalInputWordWidth) +
    processingSourceCoefficient n copyResources * model.rat i.processingSourceWidth +
      (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
        2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) +
          i.outputEncodingBound c K

noncomputable def dispatchBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.normalizationBitWork model + if rich then i.richProcessingScalingEncodingWork model primitive copyResources K bits
    else i.poorProcessingScalingEncodingWork model primitive copyResources K bits

theorem dispatchBitWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (copyResources rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.dispatchBitWork model primitive copyResources rich K bits ≤ i.dispatchBound model c copyResources K := by
  have hNormalize := i.normalizationBitWork_bound model
  cases rich
  · cases copyResources
    · have h := i.poorProcessingScalingEncodingWork_logical_bound model primitive c hPrimitive K bits
      simp only [dispatchBitWork, Bool.false_eq_true, ite_false, dispatchBound, processingSourceCoefficient]
      omega
    · have h := i.poorProcessingScalingEncodingWork_fullCopy_bound model primitive c hPrimitive K bits
      simp only [dispatchBitWork, Bool.false_eq_true, ite_false, dispatchBound, processingSourceCoefficient, ite_true]
      omega
  · have h := i.richProcessingScalingEncodingWork_bound model primitive c hPrimitive copyResources K bits
    have hCoefficient : 32 * n + 15 ≤ processingSourceCoefficient n copyResources := by
      cases copyResources <;> simp only [processingSourceCoefficient, Bool.false_eq_true, ite_false, ite_true] <;> nlinarith
    have hSource := Nat.mul_le_mul_right (model.rat i.processingSourceWidth) hCoefficient
    simp only [dispatchBitWork, ite_true, dispatchBound]
    omega

end Blotto.RationalPRGOriginalInput
