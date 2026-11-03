import Blotto.BinaryFrameEncodingCost
import Blotto.RationalPRGBinaryOutput
import Blotto.RationalPRGOriginalScalingCost

/-! Output framing prices the actual original-budget rows on every finite-bit
path. The complete-buffer-copy concatenation bound is conservative. Input
decoding, promise recognition, metadata and physical backend/ownership remain
separate from processing/scaling/output primitive and cell-copy prices. -/

namespace Blotto.RationalPRGOriginalInput

def richOutputEncodingWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  BinaryRatListFrame.rowEncodingBitWork primitive (i.richSample K bits)

def poorOutputEncodingWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  BinaryRatListFrame.rowEncodingBitWork primitive (i.poorSample K bits)

def outputEncodingBound {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) : ℕ :=
  let W := 2 ^ 77 * (i.originalInputWordWidth + K + 6)
  (4 * c + 6) * (binaryWordWidth n + 1) ^ 2 + n * (10 * c + 20) * (W + 1) ^ 2 +
    (n + 1) * n * (2 * W + 1) + 2 * binaryWordWidth n + 1 + 2 * n

theorem outputEncodingWork_bounds {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richOutputEncodingWork primitive K bits ≤ i.outputEncodingBound c K ∧
      i.poorOutputEncodingWork primitive K bits ≤ i.outputEncodingBound c K :=
  ⟨BinaryRatListFrame.rowEncodingBitWork_bound primitive c hPrimitive (i.richSample K bits) _
      (fun j => (i.sample_wordWidths_linear K bits j).1),
    BinaryRatListFrame.rowEncodingBitWork_bound primitive c hPrimitive (i.poorSample K bits) _
      (fun j => (i.sample_wordWidths_linear K bits j).2)⟩

noncomputable def richProcessingScalingEncodingWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richProcessingAndScalingWork model primitive copyResources K bits + i.richOutputEncodingWork primitive K bits

noncomputable def poorProcessingScalingEncodingWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorProcessingAndScalingWork model primitive copyResources K bits + i.poorOutputEncodingWork primitive K bits

theorem richProcessingScalingEncodingWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richProcessingScalingEncodingWork model primitive copyResources K bits ≤
      (32 * n + 15) * model.rat i.processingSourceWidth + i.processingCouplingBound model c K +
        2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) +
          i.outputEncodingBound c K :=
  Nat.add_le_add (i.richProcessingAndScalingWork_bound model primitive c hPrimitive copyResources K bits)
    (i.outputEncodingWork_bounds primitive c hPrimitive K bits).1

theorem poorProcessingScalingEncodingWork_logical_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorProcessingScalingEncodingWork model primitive false K bits ≤
      (192 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) +
            i.outputEncodingBound c K :=
  Nat.add_le_add (i.poorProcessingAndScalingWork_logical_bound model primitive c hPrimitive K bits)
    (i.outputEncodingWork_bounds primitive c hPrimitive K bits).2

theorem poorProcessingScalingEncodingWork_fullCopy_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorProcessingScalingEncodingWork model primitive true K bits ≤
      (2 * n * n + 188 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) + 4 * n * model.rat (i.scalingWidth K) +
            i.outputEncodingBound c K :=
  Nat.add_le_add (i.poorProcessingAndScalingWork_fullCopy_bound model primitive c hPrimitive K bits)
    (i.outputEncodingWork_bounds primitive c hPrimitive K bits).2

end Blotto.RationalPRGOriginalInput
