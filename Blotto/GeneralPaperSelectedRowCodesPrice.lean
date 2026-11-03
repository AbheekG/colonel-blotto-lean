import Blotto.GeneralPaperChooseRowsPrice

/-! Copy only the selected stored native code from each field. The bit
profile reserves the full encoded code word, not the floating/mesh word.
There is no re-encoding, classifier invocation or catalogue reconstruction. -/
namespace Blotto.GeneralPaperSelectedRowCodesPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (data : GeneralPaperCatalogueArrays.Arrays m K)
    (row : FixedArrayTable m (Fin K)) : FixedArrayTable m ℕ × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (fun j =>
    let code := (data.codes.read j).read (row.read j)
    (code,(if bits then 1+binaryWordWidth code else 1)+64*W+64*(if bits then arrayWord W K else W)))
  (filled.1,filled.2+64*W)

theorem data {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (values : GeneralPaperCatalogueArrays.Arrays m K)
    (row : FixedArrayTable m (Fin K)) :
    (run bits index W values row).1=GeneralPaperCatalogueRowSemantics.rowCodes values row := by
  simp only [run,PaperIndexedArrayConstruction.run_data,GeneralPaperCatalogueRowSemantics.rowCodes]

theorem code_word {m k : ℕ} (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    1+binaryWordWidth ((ready.data.codes.read j).read (row.read j))≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda := by
  have hb := GeneralPaperCatalogueArrays.code_bound ready.alphabet ready.response k ready.summaries j (row.read j)
  rw [←ready.data_spec] at hb
  have hc : (ready.data.codes.read j).read (row.read j)<2^ready.alphabet.lambda := by rw [←ready.alphabet.dyadic]; exact hb
  have hw := GeneralPaperCFOperandPrice.small_word ready.alphabet.lambda _ hc
  unfold GeneralPaperDecoderControls.operandWidth
  omega

def profile (W m K lambda : ℕ) : ℕ :=
  m*(GeneralPaperDecoderControls.operandWidth lambda+64*W+64*arrayWord W K)+44*(m+1)*arrayWord W m+64*W

theorem work {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) :
    (run true (fun x => x) W ready.data row).2≤profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun x => x) (arrayWord W m)
    (GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda+64*W+64*arrayWord W ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (fun j => ((ready.data.codes.read j).read (row.read j),1+binaryWordWidth ((ready.data.codes.read j).read (row.read j))+64*W+
      64*arrayWord W ((GeneralPaperSourceParameters.prepare k).summarySize+2)))
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun j => Nat.add_le_add_right (Nat.add_le_add_right (code_word ready row j) _) _)
  exact Nat.add_le_add_right h _

theorem arithmetic_work {m K : ℕ} (values : GeneralPaperCatalogueArrays.Arrays m K) (row : FixedArrayTable m (Fin K)) :
    (run false (fun _ => 1) 1 values row).2≤173*m+108 := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 129
    (fun j => ((values.codes.read j).read (row.read j),129)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun j => ((values.codes.read j).read (row.read j),129))).2+64≤_
  nlinarith only [h]

end Blotto.GeneralPaperSelectedRowCodesPrice
