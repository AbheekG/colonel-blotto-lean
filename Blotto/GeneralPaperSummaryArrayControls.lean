import Blotto.GeneralPaperSummaryArrayExecution

/-! The retained summary size supplies index, increment and traversal word
bounds. Global references use the explicit W component of the array word.
-/
namespace Blotto.GeneralPaperSummaryArrayControls
open GeneralPaperSummaryArrayExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem array_word_positive (W count : ℕ) : 1≤arrayWord W count := by unfold arrayWord; omega

theorem array_index (W count i : ℕ) (hi : i≤count) : binaryWordWidth (i+1)≤arrayWord W count := by
  have h := binaryWordWidth_mono (Nat.add_le_add_right hi 1)
  unfold arrayWord; omega

theorem size_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (GeneralPaperSourceParameters.prepare k).summarySize≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  have hp := GeneralPaperNatPowerOperands.power_width 2 (34+k)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  rw [hs]
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem target_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m lambda k Qv : ℕ)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) r.val 1≤
      2*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  have hs := size_word m lambda k Qv
  have hWord : primitive (1+binaryWordWidth (GeneralPaperSourceParameters.prepare k).summarySize)≤
      primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := hMono (hs.trans (by omega))
  exact (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) r.val 1
    (GeneralPaperSourceParameters.prepare k).summarySize (by omega) (by have h:=r.isLt; omega) (Nat.succ_le_of_lt r.isLt)).trans
      (Nat.mul_le_mul_left 2 hWord)

end Blotto.GeneralPaperSummaryArrayControls
