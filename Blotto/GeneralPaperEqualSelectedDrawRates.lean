import Blotto.GeneralPaperEqualSelectedPipeline

/-! The pure copy is dominated by the same sharp local draw majorant as
the grouped controller/output producer. Fast-bit draw bounds depend on
n, exponent and original budget precision, not accuracy encoding length. -/
namespace Blotto.GeneralPaperEqualSelectedDrawRates
open GeneralPaperEqualBitDrawRates (word log)
open GeneralPaperEqualSelectedDraw
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem pure_dominated (model : RationalCostModel) (n k b : ℕ) :
    pureBound n k b ≤ GeneralPaperEqualFullBitContract.bound model n k b := by
  let R := model.rat (word n k b)
  let L := log n k b
  let M := (n + 1) * R * L
  have hL : 1 ≤ L := by dsimp only [L,log]; omega
  have hb : b + 1 ≤ R := by
    have h := model.word_le (word n k b)
    dsimp only [R,word,GeneralPaperEqualBitDrawRates.size] at *
    omega
  have hR : 1 ≤ R := by omega
  have hIndex : binaryWordWidth (n + 1) ≤ L := by
    exact (binaryWordWidth_mono (by omega : n + 1 ≤ n + word n k b + 32)).trans (by dsimp [L,log]; omega)
  have hIndexMul := Nat.mul_le_mul_left (n + 1) hIndex
  have hNL : (n + 1) * L ≤ M := by
    dsimp only [M]
    nlinarith only [Nat.mul_le_mul_left ((n + 1) * L) hR]
  have hNM : n ≤ M := by nlinarith only [hNL,hL]
  have hLM : L ≤ M := by nlinarith only [hNL]
  have hRM : R ≤ M := by
    have h1 : R ≤ (n + 1) * R := Nat.le_mul_of_pos_left _ (by omega)
    have h2 := Nat.mul_le_mul_left ((n + 1) * R) hL
    dsimp only [M]; nlinarith only [h1,h2]
  have hBM : b ≤ M := by omega
  have hOne : 1 ≤ M := by omega
  have hPure : pureBound n k b ≤ 1024 * M := by
    dsimp only [pureBound]
    change b + 3 * n + n * (32 * (2 * L + 1) + 32) +
      (n + 1) * (6 * (2 * L + 1) + 10 * binaryWordWidth (n + 1) + 28) +
      64 * (2 * L + 1) + 64 ≤ _
    nlinarith only [hIndexMul,hNL,hNM,hLM,hBM,hOne]
  apply hPure.trans
  change 1024 * M ≤ 8589934592 * (n + 1) * R * L
  dsimp only [M]
  nlinarith only [Nat.zero_le ((n + 1) * R * L)]

theorem fast_work_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (n k b : ℕ) :
    workBound model n k b ≤
      17179869184 * C * (n + 1) * word n k b * (log n k b) ^ (d + 1) := by
  have hp := pure_dominated model n k b
  have hf := GeneralPaperEqualFullBitContract.fast_bound hg n k b
  unfold workBound
  nlinarith only [hp,hf]

end Blotto.GeneralPaperEqualSelectedDrawRates
