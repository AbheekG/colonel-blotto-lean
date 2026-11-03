import Blotto.RationalLottoSourceControllerWork
import Blotto.RationalPRGSourceOperandLedger

/-! Source Boolean/encoding work follows the exact paper packet. Its allowance
is linear in field count and scalar precision, times the input word width.
Native extraction/index/control and physical costs remain separate. -/

namespace Blotto.RationalLottoResourceSystem

def paperSourceControllerWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sourceControllerEncodingAndWordWork K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem paperSourceControllerWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperSourceControllerWork K bits ≤ 4 * binaryWordWidth D * (n - 1 + 80) +
      (24 * binaryWordWidth D + 28) * (2 * (n - 1 + 80) + 2 * coinBitBudget n K + 2) :=
  i.sourceControllerEncodingAndWordWork_bound D hD hB hL hR K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

def sourceControllerAllowance (n K inputWidth : ℕ) : ℕ :=
  4 * (1 + inputWidth) * (n - 1 + 80) +
    (24 * (1 + inputWidth) + 28) * (2 * (n - 1 + 80) + 2 * RationalLottoResourceSystem.coinBitBudget n K + 2)

theorem sourceControllerAllowance_linear (n K inputWidth : ℕ) :
    sourceControllerAllowance n K inputWidth ≤ (24 * inputWidth + 52) * (9 * n + 6 * K + 6242) := by
  have hn : n - 1 ≤ n := Nat.sub_le _ _
  unfold sourceControllerAllowance RationalLottoResourceSystem.coinBitBudget
  nlinarith

def richPaperSourceControllerWork {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richNativeSystem.paperSourceControllerWork K bits

def poorPaperSourceControllerWork {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorNativeSystem.paperSourceControllerWork K bits

theorem richPaperSourceControllerWork_bound {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richPaperSourceControllerWork K bits ≤ sourceControllerAllowance n K i.inputWordWidth := by
  have h := i.richNativeSystem.paperSourceControllerWork_bound i.latticeDenominator i.latticeDenominator_pos
    (le_refl _) i.lengths_on_lattice i.richInitial_on_lattice K bits
  have hw := i.latticeDenominator_wordWidth
  change i.richPaperSourceControllerWork K bits ≤ _ at h
  have hEncoding := Nat.mul_le_mul_right (n - 1 + 80) (Nat.mul_le_mul_left 4 hw)
  have hRate : 24 * binaryWordWidth i.latticeDenominator + 28 ≤ 24 * (1 + i.inputWordWidth) + 28 := by omega
  have hBody := Nat.mul_le_mul_right
    (2 * (n - 1 + 80) + 2 * RationalLottoResourceSystem.coinBitBudget n K + 2) hRate
  exact h.trans (Nat.add_le_add hEncoding hBody)

theorem poorPaperSourceControllerWork_bound {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorPaperSourceControllerWork K bits ≤ sourceControllerAllowance n K i.inputWordWidth := by
  have h := i.poorNativeSystem.paperSourceControllerWork_bound i.latticeDenominator i.latticeDenominator_pos
    i.b_le i.lengths_on_lattice i.poorInitial_on_lattice K bits
  have hw := i.latticeDenominator_wordWidth
  change i.poorPaperSourceControllerWork K bits ≤ _ at h
  have hEncoding := Nat.mul_le_mul_right (n - 1 + 80) (Nat.mul_le_mul_left 4 hw)
  have hRate : 24 * binaryWordWidth i.latticeDenominator + 28 ≤ 24 * (1 + i.inputWordWidth) + 28 := by omega
  have hBody := Nat.mul_le_mul_right
    (2 * (n - 1 + 80) + 2 * RationalLottoResourceSystem.coinBitBudget n K + 2) hRate
  exact h.trans (Nat.add_le_add hEncoding hBody)

end Blotto.RationalPRGInput
