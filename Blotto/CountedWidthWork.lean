import Blotto.BinaryCarryCounterFinalization
import Blotto.BinaryWordPrecision

/-! The actual precision path counts four word widths. Carry cells and final
balanced counter-merge sizes are bounded separately from word traversal.
Backend arithmetic, counters inside the decoder and allocation remain separate. -/

namespace Blotto.PositiveBinaryWord

def countedWidthMergeWork (w : PositiveBinaryWord) : ℕ :=
  BinaryPayload.mergeSize (BinaryCarryCounter.count w.tail [true]).length

theorem countedWidthMergeWork_bound (w : PositiveBinaryWord) : w.countedWidthMergeWork ≤ 8 * w.width :=
  BinaryCarryCounter.counter_mergeSize_bound w.tail

def leWidthCarryWork (a b : PositiveBinaryWord) : ℕ :=
  BinaryCarryCounter.countCarryCells a.tail [true] + BinaryCarryCounter.countCarryCells b.tail [true]

theorem leWidthCarryWork_bound (a b : PositiveBinaryWord) : a.leWidthCarryWork b ≤ 2 * (a.width + b.width) := by
  have ha := a.countedWidth_carry_bound
  have hb := b.countedWidth_carry_bound
  unfold leWidthCarryWork
  omega

def ratioWidthCarryWork (a b : PositiveBinaryWord) : ℕ :=
  a.leWidthCarryWork b + a.leWidthCarryWork (b.shifted (a.width - b.width))

theorem ratioWidthCarryWork_bound (a b : PositiveBinaryWord) : a.ratioWidthCarryWork b ≤ 6 * (a.width + b.width) := by
  have hFirst := a.leWidthCarryWork_bound b
  have hSecond := a.leWidthCarryWork_bound (b.shifted (a.width - b.width))
  rw [width_shifted] at hSecond
  unfold ratioWidthCarryWork
  omega

def ratioWidthMergeWork (a b : PositiveBinaryWord) : ℕ :=
  a.countedWidthMergeWork + b.countedWidthMergeWork + a.countedWidthMergeWork +
    (b.shifted (a.width - b.width)).countedWidthMergeWork

theorem ratioWidthMergeWork_bound (a b : PositiveBinaryWord) : a.ratioWidthMergeWork b ≤ 24 * (a.width + b.width) := by
  have ha := a.countedWidthMergeWork_bound
  have hb := b.countedWidthMergeWork_bound
  have hs := (b.shifted (a.width - b.width)).countedWidthMergeWork_bound
  rw [width_shifted] at hs
  unfold ratioWidthMergeWork
  omega

end Blotto.PositiveBinaryWord
