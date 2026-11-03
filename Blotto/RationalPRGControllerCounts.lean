import Blotto.WordMachineIndexedCounts
import Blotto.RationalLottoPaperProgram

/-! The actual global shared-cap controller has linearly many outer step
queries, input reads and cursor visits. These counts exclude callback bodies,
preparation, emission and heap ownership, which need their own cost contracts. -/

namespace Blotto.RationalLottoResourceSystem

def paperFixedCounts {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ControllerCounts :=
  (i.machine K outerBits scalarBits).runCounts R (i.samplingStart K outerBits scalarBits) choiceBits

theorem paperFixedCounts_reads {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    (i.paperFixedCounts K R outerBits scalarBits choiceBits).reads =
      ((i.machine K outerBits scalarBits).run R (i.samplingStart K outerBits scalarBits) choiceBits).2 :=
  (i.machine K outerBits scalarBits).runCounts_reads_eq R (i.samplingStart K outerBits scalarBits) choiceBits

theorem paperFixedCounts_bounds {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    (i.paperFixedCounts K R outerBits scalarBits choiceBits).callbacks ≤ n + 1001 ∧
      (i.paperFixedCounts K R outerBits scalarBits choiceBits).reads ≤ R ∧
      (i.paperFixedCounts K R outerBits scalarBits choiceBits).visits ≤ 2 * (n + 1000) + 2 * R + 2 := by
  have hBounds := (i.machine K outerBits scalarBits).runCounts_bounds R (n + 1000)
    (i.samplingStart K outerBits scalarBits) (i.program_rank_paper_bound K outerBits scalarBits) choiceBits
  exact ⟨hBounds.1, (i.machine K outerBits scalarBits).runCounts_reads_le R
    (i.samplingStart K outerBits scalarBits) choiceBits, hBounds.2⟩

def paperCounts {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ControllerCounts :=
  let innerBits := firstBitBlock (innerBitBudget n K) K bits
  let outerBits := secondBitBlock (innerBitBudget n K) K bits
  let choiceBits := firstBitBlock (coinBitBudget n K) K innerBits
  let scalarBits := secondBitBlock (coinBitBudget n K) K innerBits
  i.paperFixedCounts K (coinBitBudget n K) outerBits scalarBits choiceBits

theorem paperCounts_bounds {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    (i.paperCounts K bits).callbacks ≤ n + 1001 ∧
      (i.paperCounts K bits).reads ≤ 3 * (n + 1000 + K) ∧
      (i.paperCounts K bits).visits ≤ 8 * (n + 1000) + 6 * K + 2 := by
  unfold paperCounts
  dsimp only
  have h := i.paperFixedCounts_bounds K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))
  have hVisits := h.2.2
  have hCost : 2 * (n + 1000) + 2 * coinBitBudget n K + 2 ≤ 8 * (n + 1000) + 6 * K + 2 := by
    unfold coinBitBudget
    omega
  exact ⟨h.1, h.2.1, hVisits.trans hCost⟩

end Blotto.RationalLottoResourceSystem
