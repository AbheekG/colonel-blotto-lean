import Blotto.RationalPRGSharedProcessingLedger

/-! Transfers the whole primary processing allowance to original input words.
Normalization changes only the poor budget ratio. This module prices no
parser or physical backend and makes no claim about output scaling yet. -/

namespace Blotto.RationalPRGOriginalInput
open scoped BigOperators

theorem normalized_inputWordWidth_bound {n : ℕ} (i : RationalPRGOriginalInput n) :
    i.normalizedInput.inputWordWidth ≤ 1 + 2 * i.originalInputWordWidth := by
  have hr := rationalWordWidth_of_height
    ((rationalHeight_of_wordWidth i.b).div (rationalHeight_of_wordWidth i.a))
  change rationalWordWidth (i.b / i.a) ≤ 1 + 2 * (rationalWordWidth i.b + rationalWordWidth i.a) at hr
  change rationalWordWidth (i.b / i.a) + (∑ j, rationalWordWidth (i.values j)) ≤ 1 + 2 * i.originalInputWordWidth
  unfold originalInputWordWidth
  omega

def processingInputWidth {n : ℕ} (i : RationalPRGOriginalInput n) : ℕ := 1 + 2 * i.originalInputWordWidth

def processingSourceWidth {n : ℕ} (i : RationalPRGOriginalInput n) : ℕ :=
  max (binaryWordWidth (n + 4)) (8 * i.processingInputWidth + 31)

def processingCouplingWidth {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  1 + 2 * expressionHeightBudget (max (3 + i.processingInputWidth) (K + 2)) 75

def processingControlHeight {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  RationalTerminalLotto.terminalCouplingWordHeight (max (3 + i.processingInputWidth) (K + 2))

def processingCouplingBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K : ℕ) : ℕ :=
  9072 * RationalNestedInput.preparationNumericBitWork c K +
    (70000020 + 8 * n) * model.rat (i.processingCouplingWidth K) +
      320 * i.processingControlHeight K + (24 * i.processingControlHeight K + 28) *
        (162 + 2 * RationalLottoResourceSystem.coinBitBudget n K)

theorem normalized_sourceWidth_le {n : ℕ} (i : RationalPRGOriginalInput n) :
    i.normalizedInput.sourceAndPackingWidth ≤ i.processingSourceWidth := by
  have h := i.normalized_inputWordWidth_bound
  unfold RationalPRGInput.sourceAndPackingWidth processingSourceWidth processingInputWidth
  omega

theorem normalized_couplingWidth_le {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.normalizedInput.paperCouplingWidth K ≤ i.processingCouplingWidth K := by
  have h := i.normalized_inputWordWidth_bound
  have hw : max (3 + i.normalizedInput.inputWordWidth) (K + 2) ≤ max (3 + i.processingInputWidth) (K + 2) := by
    unfold processingInputWidth
    omega
  have hp := Nat.mul_le_mul_right (2 ^ 75) (Nat.add_le_add_right hw 1)
  unfold RationalPRGInput.paperCouplingWidth processingCouplingWidth expressionHeightBudget
  omega

theorem normalized_controlHeight_le {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.normalizedInput.paperCouplingControlHeight K ≤ i.processingControlHeight K := by
  have h := i.normalized_inputWordWidth_bound
  have hw : max (3 + i.normalizedInput.inputWordWidth) (K + 2) ≤ max (3 + i.processingInputWidth) (K + 2) := by
    unfold processingInputWidth
    omega
  have hp := Nat.mul_le_mul_right (2 ^ 69) (Nat.add_le_add_right hw 1)
  unfold RationalPRGInput.paperCouplingControlHeight processingControlHeight
    RationalTerminalLotto.terminalCouplingWordHeight expressionHeightBudget
  omega

theorem normalized_couplingBound_le {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K : ℕ) :
    i.normalizedInput.paperCouplingBound model c K ≤ i.processingCouplingBound model c K := by
  have hPrice := model.monotone (i.normalized_couplingWidth_le K)
  have hControl := i.normalized_controlHeight_le K
  unfold RationalPRGInput.paperCouplingBound processingCouplingBound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hPrice) _)
    (Nat.mul_le_mul_left _ hControl)) (Nat.mul_le_mul_right _ (by omega))

theorem normalized_richProcessingWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.normalizedInput.richSharedProcessingWork model primitive copyResources K bits ≤
      (32 * n + 15) * model.rat i.processingSourceWidth + i.processingCouplingBound model c K +
        2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) := by
  have hFallback := model.monotone (show 1 + 2 * (3 + i.normalizedInput.inputWordWidth) ≤
      1 + 2 * (3 + i.processingInputWidth) by have h := i.normalized_inputWordWidth_bound; unfold processingInputWidth; omega)
  exact (i.normalizedInput.richSharedProcessingWork_bound model primitive c hPrimitive copyResources K bits).trans
    (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (model.monotone i.normalized_sourceWidth_le))
      (i.normalized_couplingBound_le model c K)) (Nat.mul_le_mul_left _ hFallback))

theorem normalized_poorProcessingWork_logical_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.normalizedInput.poorSharedProcessingWork model primitive false K bits ≤
      (192 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) := by
  have h := i.normalized_inputWordWidth_bound
  change i.normalizedInput.inputWordWidth ≤ i.processingInputWidth at h
  have hFallback := model.monotone (show 1 + 2 * (3 + i.normalizedInput.inputWordWidth) ≤
    1 + 2 * (3 + i.processingInputWidth) by omega)
  exact (i.normalizedInput.poorSharedProcessingWork_logical_bound model primitive c hPrimitive K bits).trans
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left _ (model.monotone i.normalized_sourceWidth_le))
      (Nat.mul_le_mul_right _ (by omega))) (i.normalized_couplingBound_le model c K))
        (Nat.mul_le_mul_left _ hFallback))

theorem normalized_poorProcessingWork_fullCopy_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.normalizedInput.poorSharedProcessingWork model primitive true K bits ≤
      (2 * n * n + 188 * n + 15) * model.rat i.processingSourceWidth +
        (24 * i.processingInputWidth + 52) * (9 * n + 6 * K + 6002) + i.processingCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.processingInputWidth)) := by
  have h := i.normalized_inputWordWidth_bound
  change i.normalizedInput.inputWordWidth ≤ i.processingInputWidth at h
  have hFallback := model.monotone (show 1 + 2 * (3 + i.normalizedInput.inputWordWidth) ≤
    1 + 2 * (3 + i.processingInputWidth) by omega)
  exact (i.normalizedInput.poorSharedProcessingWork_fullCopy_bound model primitive c hPrimitive K bits).trans
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left _ (model.monotone i.normalized_sourceWidth_le))
      (Nat.mul_le_mul_right _ (by omega))) (i.normalized_couplingBound_le model c K))
        (Nat.mul_le_mul_left _ hFallback))

end Blotto.RationalPRGOriginalInput
