import Blotto.RationalPRGDispatchWork

/-! Separates the selected sampler's work bound from its certified input
record. Monotonicity then permits uniform incoming-bit bounds without hiding
numeric parameters or seed-dependent work. Physical contracts remain separate. -/

namespace Blotto.RationalPRGOriginalInput

def dispatchEnvelope (model : RationalCostModel) (c : ℕ) (copyResources : Bool) (n L K : ℕ) : ℕ :=
  let I := 1 + 2 * L
  let S := max (binaryWordWidth (n + 4)) (8 * I + 31)
  let W := max (3 + I) (K + 2)
  let H := RationalTerminalLotto.terminalCouplingWordHeight W
  let C := 9072 * RationalNestedInput.preparationNumericBitWork c K +
    (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget W 75) +
      320 * H + (24 * H + 28) * (162 + 2 * RationalLottoResourceSystem.coinBitBudget n K)
  let O := 2 ^ 77 * (L + K + 6)
  5 * model.rat (1 + 2 * L) + processingSourceCoefficient n copyResources * model.rat S +
    (24 * I + 52) * (9 * n + 6 * K + 6002) + C + 2 * n * model.rat (1 + 2 * (3 + I)) +
      4 * n * model.rat (1 + 2 * expressionHeightBudget (max (3 + L) (K + 2)) 76) +
        ((4 * c + 6) * (binaryWordWidth n + 1) ^ 2 + n * (10 * c + 20) * (O + 1) ^ 2 +
          (n + 1) * n * (2 * O + 1) + 2 * binaryWordWidth n + 1 + 2 * n)

theorem dispatchBound_eq_envelope {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c : ℕ) (copyResources : Bool) (K : ℕ) :
    i.dispatchBound model c copyResources K = dispatchEnvelope model c copyResources n i.originalInputWordWidth K := rfl

theorem preparationNumericBitWork_mono (c : ℕ) {K Q : ℕ} (hK : K ≤ Q) :
    RationalNestedInput.preparationNumericBitWork c K ≤ RationalNestedInput.preparationNumericBitWork c Q := by
  have hWidth := binaryWordWidth_mono hK
  unfold RationalNestedInput.preparationNumericBitWork
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hK)
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) hWidth)) (Nat.mul_le_mul_left _ (by omega))

theorem processingSourceCoefficient_mono (copyResources : Bool) {n N : ℕ} (hn : n ≤ N) :
    processingSourceCoefficient n copyResources ≤ processingSourceCoefficient N copyResources := by
  cases copyResources <;> simp only [processingSourceCoefficient, Bool.false_eq_true, ite_false, ite_true]
  · omega
  · have hSquare := Nat.mul_self_le_mul_self hn
    nlinarith

theorem dispatchEnvelope_mono (model : RationalCostModel) (c : ℕ) (copyResources : Bool)
    {n N L U K Q : ℕ} (hn : n ≤ N) (hL : L ≤ U) (hK : K ≤ Q) :
    dispatchEnvelope model c copyResources n L K ≤ dispatchEnvelope model c copyResources N U Q := by
  have hInput : 1 + 2 * L ≤ 1 + 2 * U := by omega
  have hNWidth := binaryWordWidth_mono hn
  have hSourceWidth : max (binaryWordWidth (n + 4)) (8 * (1 + 2 * L) + 31) ≤
      max (binaryWordWidth (N + 4)) (8 * (1 + 2 * U) + 31) := by
    have h := binaryWordWidth_mono (show n + 4 ≤ N + 4 by omega)
    omega
  have hBase : max (3 + (1 + 2 * L)) (K + 2) ≤ max (3 + (1 + 2 * U)) (Q + 2) := by omega
  have hCouplingWidth := model.heightPrice_mono hBase (le_refl 75)
  have hControl : RationalTerminalLotto.terminalCouplingWordHeight (max (3 + (1 + 2 * L)) (K + 2)) ≤
      RationalTerminalLotto.terminalCouplingWordHeight (max (3 + (1 + 2 * U)) (Q + 2)) := by
    have h := expressionHeightBudget_input_mono hBase 69
    unfold RationalTerminalLotto.terminalCouplingWordHeight
    omega
  have hScale := model.heightPrice_mono (show max (3 + L) (K + 2) ≤ max (3 + U) (Q + 2) by omega) (le_refl 76)
  have hEncoding : 2 ^ 77 * (L + K + 6) ≤ 2 ^ 77 * (U + Q + 6) := Nat.mul_le_mul_left _ (by omega)
  have hCoin : RationalLottoResourceSystem.coinBitBudget n K ≤ RationalLottoResourceSystem.coinBitBudget N Q := by
    unfold RationalLottoResourceSystem.coinBitBudget
    omega
  have hNormalize := model.monotone hInput
  have hSource := model.monotone hSourceWidth
  have hFallback := model.monotone (show 1 + 2 * (3 + (1 + 2 * L)) ≤ 1 + 2 * (3 + (1 + 2 * U)) by omega)
  have hNumeric := preparationNumericBitWork_mono c hK
  have hCoefficient := processingSourceCoefficient_mono copyResources hn
  unfold dispatchEnvelope
  dsimp only
  gcongr

end Blotto.RationalPRGOriginalInput
