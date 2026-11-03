import Blotto.BinaryRatListFrame
import Blotto.RationalPRGOutputHeight

/-! Portable dimensioned output frames for both original-budget PRG players.
Readback is exact on every bit path, so hard feasibility is retained. Encoded
length is charged to actual reduced coordinate widths, not a padded bound. -/

namespace Blotto

namespace BinaryRatListFrame

def FullBudgetList (B : ℚ) (values : List ℚ) : Prop :=
  (∀ q ∈ values, 0 ≤ q) ∧ values.sum = B

theorem fullBudget_ofFn {n : ℕ} (B : ℚ) (row : Fin n → ℚ)
    (h : Blotto.FullBudget (B : ℝ) (fun j => (row j : ℝ))) : FullBudgetList B (List.ofFn row) := by
  constructor
  · intro q hq
    rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩
    have hNonneg : (0 : ℝ) ≤ (row j : ℝ) := h.1 j
    exact_mod_cast hNonneg
  · have hSumR : (∑ j, (row j : ℝ)) = (B : ℝ) := h.2
    have hSum : (∑ j, row j) = B := by exact_mod_cast hSumR
    simpa only [List.sum_ofFn] using hSum

end BinaryRatListFrame

namespace RationalPRGOriginalInput

def richOutputBits {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  BinaryRatListFrame.encodeRow (i.richSample K bits)

def poorOutputBits {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  BinaryRatListFrame.encodeRow (i.poorSample K bits)

theorem richOutput_readback {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (i.richOutputBits K bits ++ suffix) = some (n, List.ofFn (i.richSample K bits), suffix) :=
  BinaryRatListFrame.readRow_encode_append _ suffix

theorem poorOutput_readback {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (i.poorOutputBits K bits ++ suffix) = some (n, List.ofFn (i.poorSample K bits), suffix) :=
  BinaryRatListFrame.readRow_encode_append _ suffix

theorem output_readback_budgets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryRatListFrame.FullBudgetList i.a (List.ofFn (i.richSample K bits)) ∧
      BinaryRatListFrame.FullBudgetList i.b (List.ofFn (i.poorSample K bits)) :=
  ⟨BinaryRatListFrame.fullBudget_ofFn _ _ (i.richSample_fullBudget K bits),
    BinaryRatListFrame.fullBudget_ofFn _ _ (i.poorSample_fullBudget K bits)⟩

theorem output_bit_lengths {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (i.richOutputBits K bits).length ≤ 2 * binaryWordWidth n + 1 +
      2 * (n * (2 ^ 77 * (i.originalInputWordWidth + K + 6))) + n ∧
    (i.poorOutputBits K bits).length ≤ 2 * binaryWordWidth n + 1 +
      2 * (n * (2 ^ 77 * (i.originalInputWordWidth + K + 6))) + n := by
  have hRich := BinaryRatListFrame.encodeRow_length (i.richSample K bits)
  have hPoor := BinaryRatListFrame.encodeRow_length (i.poorSample K bits)
  have hWidths := i.sample_total_wordWidths K bits
  simp only [List.sum_ofFn] at hRich hPoor
  change (i.richOutputBits K bits).length = _ at hRich
  change (i.poorOutputBits K bits).length = _ at hPoor
  constructor <;> omega

end RationalPRGOriginalInput
end Blotto
