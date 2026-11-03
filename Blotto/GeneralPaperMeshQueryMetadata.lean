import Blotto.GeneralPaperMeshQueryEnvelope

/-! Native per-query annotations use only short constructed counters. The
same retained parameter envelope covers cached CDF/interval layers and the
four-count loss queries. Reference reads also cover cached rank words.
-/
namespace Blotto.GeneralPaperMeshQueryMetadata
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def cap (k : ℕ) : ℕ := 1024*(k+32)
def referenceWord (W k : ℕ) : ℕ := arrayWord W ((GeneralPaperSourceParameters.prepare k).summarySize+2)

theorem operand_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap k)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := binaryWordWidth_mul 1024 (k+32)
  have hk := GeneralPaperInitializerControlCounters.word_le_self (k+32)
  have hc : binaryWordWidth 1024=11 := by decide
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold cap GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem add_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv a b : ℕ)
    (hSum : a+b≤cap k) : GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) a b≤
      2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :=
  (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) a b (cap k)
    (by omega) (by omega) hSum).trans (Nat.mul_le_mul_left 2 (hMono (operand_word m lambda k Qv)))

theorem read_word (W k : ℕ) : W≤referenceWord W k := by unfold referenceWord arrayWord; omega

theorem selected_add_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv numerator total extra : ℕ)
    (hExtra : extra≤64) : GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b)
      (GeneralPaperCDFMesh.selected k numerator total).work extra≤
        2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  apply add_work price hMono m lambda k Qv
  rw [GeneralPaperCDFMesh.selected_work]
  unfold cap
  omega

end Blotto.GeneralPaperMeshQueryMetadata
