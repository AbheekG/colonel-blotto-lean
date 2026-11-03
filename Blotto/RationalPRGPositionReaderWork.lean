import Blotto.RationalSharedVisitCount
import Blotto.FairBitBlockReaderWork
import Blotto.RationalPRGOutputHeight

/-! A per-visit allowance bounds actual controller position/cap arithmetic
and permits two input accesses on mismatch. No monotonicity of the supplied
primitive price is assumed: each actual argument width uses its own price.
Physical array addresses/backend/records and callback bodies remain separate. -/

namespace Blotto

def positionReaderBitPrice (primitive : ℕ → ℕ) (cap total pos : ℕ) : ℕ :=
  6 * binaryWordWidth (total + 2) + primitive (max (binaryWordWidth pos) (binaryWordWidth cap)) +
    primitive (binaryWordWidth (pos + 1)) + 2 * bitBlockReadBitPrice primitive 0 pos + 6

def positionReaderUnitBound (c total : ℕ) : ℕ :=
  (16 + 4 * c) * binaryWordWidth (total + 2) + 8

theorem positionReaderBitPrice_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (cap total pos : ℕ) (hPos : pos ≤ cap) (hCap : cap ≤ total) :
    positionReaderBitPrice primitive cap total pos ≤ positionReaderUnitBound c total := by
  have hPosWidth := binaryWordWidth_mono (show pos ≤ total + 2 by omega)
  have hCapWidth := binaryWordWidth_mono (show cap ≤ total + 2 by omega)
  have hNextWidth := binaryWordWidth_mono (show pos + 1 ≤ total + 2 by omega)
  have hCompare := (hPrimitive (max (binaryWordWidth pos) (binaryWordWidth cap))).trans
    (Nat.mul_le_mul_left c (max_le hPosWidth hCapWidth))
  have hAdvance := (hPrimitive (binaryWordWidth (pos + 1))).trans (Nat.mul_le_mul_left c hNextWidth)
  have hReader := bitBlockReadBitPrice_bound primitive c hPrimitive 0 pos (total + 1) (by omega)
  simp only [Nat.add_assoc] at hReader
  unfold positionReaderBitPrice positionReaderUnitBound
  nlinarith

theorem positionReaderUnitBound_mono (c : ℕ) : Monotone (positionReaderUnitBound c) := by
  intro a b hab
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (binaryWordWidth_mono (Nat.add_le_add_right hab 2))) 8

end Blotto
namespace Blotto.RationalLottoResourceSystem

def paperPositionReaderAllowance {n : ℕ} (i : RationalLottoResourceSystem n) (c K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedPaperVisitCount K bits * positionReaderUnitBound c (sampleBitBudget n K)

theorem paperPositionReaderAllowance_bound {n : ℕ} (i : RationalLottoResourceSystem n) (c K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperPositionReaderAllowance c K bits ≤ (10 * n + 6 * K + 6166) * positionReaderUnitBound c (sampleBitBudget n K) :=
  Nat.mul_le_mul_right _ (i.sharedPaperVisitCount_bound K bits)

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem paperPositionReaderAllowance_bounds {n : ℕ} (i : RationalPRGInput n) (c K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.paperPositionReaderAllowance c K bits ≤ (10 * n + 6 * K + 6166) *
        positionReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K) ∧
      i.poorNativeSystem.paperPositionReaderAllowance c K bits ≤ (10 * n + 6 * K + 6166) *
        positionReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K) :=
  ⟨i.richNativeSystem.paperPositionReaderAllowance_bound c K bits,
    i.poorNativeSystem.paperPositionReaderAllowance_bound c K bits⟩

end Blotto.RationalPRGInput
